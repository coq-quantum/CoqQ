From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra finmap.
From mathcomp.classical Require Import boolp.
From mathcomp.analysis Require Import -(notations)forms.
From mathcomp.analysis Require Import reals.
(* From mathcomp.real_closed Require Import complex. *)
From quantum.external Require Import complex.
Require Import Relation_Definitions.
Require Import Setoid.
(* topology and setoid has notation conflicts *)
(* several lemma in classical_sets and finset have the same name. *)

Require Import mcextra mcaextra notation mxpred.
Require Import hermitian quantum hspace inhabited prodvect tensor qreg qmem qtype.
From quantum.dirac Require Import hstensor.
From quantum.example.qlaws Require Import basic_def.
Import Order.TTheory GRing.Theory Num.Theory Num.Def.
Import DefaultQMem.Exports.

(****************************************************************************)
(*                Semantics and QLaws for Circuit Program                   *)
(****************************************************************************)

Local Notation C := hermitian.C.
Local Open Scope set_scope.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope reg_scope.

Declare Custom Entry cmd.
Reserved Notation "<{[ e ]}>" (at level 0, e custom cmd at level 99).
Reserved Notation "( x )" (in custom cmd at level 0).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

(* automation; use for typeclass_instances *)
(* syntactical decision of well-formedness, disjointness, etc. *)
Class cmd_expose (P : Prop) := CmdExpose : P.
Notation "`{{ P }}" := (cmd_expose P).

Inductive ucmd_ : Type :=
    | uskip_
    | unitary_ T (x : qreg T) (U : 'FU('Ht T))
    | sequ_ of ucmd_ & ucmd_
    | qcond_ T (F : finType) (x : qreg T) of 'ONB(F;'Ht T) & (F -> ucmd_).

HB.lock
Definition qcond2_ (x : qreg Bool) (phi : 'ONB(bool; 'Ht Bool)) (c0 c1 : ucmd_) :=
  qcond_ x phi (fun b => if b then c1 else c0).

Declare Scope cmd_scope.
Delimit Scope cmd_scope with cmd.
Open Scope cmd_scope.
Notation "<{[ e ]}>" := e (at level 0, e custom cmd at level 99) : cmd_scope.
Notation "e" := e (at level 0, e custom cmd at level 99, only printing) : cmd_scope.
Notation "( x )" := x (in custom cmd at level 0).
Notation "x" := x (in custom cmd at level 0, x constr at level 0).
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom reg at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9).
Notation "'uskip'" := uskip_ (in custom cmd at level 0).
Notation " c1 ';' c2 " := (sequ_ c1 c2) (in custom cmd at level 30, c2 at next level, 
  left associativity, format "'[v' c1  ;  '/' c2 ']'").
Notation " [ x ] '*=' U " := (unitary_ x U) (in custom cmd at level 20, x custom reg, U constr, 
  format "[ x ]  '*='  U").
Notation " 'qif' phi [ x ] '=' i 'then' F 'fiq'" := (qcond_ x phi (fun i => F))
  (in custom cmd at level 20, x custom reg, phi constr, i name, F constr,
  format "'[v' 'qif'  phi [ x ]  '='  i  'then'  '/' '['     F ']' '/' 'fiq' ']'").
Notation " 'qif' [ x ] '=' i 'then' F 'fiq'" := (qcond_ x t2tv (fun i => F))
  (in custom cmd at level 20, x custom reg, i name, F constr, only parsing,
  format "'[v''qif'  [ x ]  '='  i  'then'  '/' '['     F ']' '/' 'fiq' ']'").
Notation " 'qif' [ x ] '=' i 'then' F 'fiq'" := (qcond_ x (@reverse_coercion _ _
  (inhabited_t2tv__canonical__quantum_ONB (eval_qtype _)) (@t2tv (eval_qtype _))) (fun i => F))
  (in custom cmd at level 20, x custom reg, i name, F constr, only printing,
  format "'[v' 'qif'  [ x ]  '='  i  'then'  '/' '['     F ']' '/' 'fiq' ']'").
Notation " 'qif' phi [ x ] 'then' u1 'else' u0 'fiq'" := (qcond2_ x phi u0 u1)
  (in custom cmd at level 20, x custom reg, phi constr,
  format "'[v' 'qif'  phi [ x ]  'then'  '/' '['     u1 ']' '/' 'else' '/' '['     u0 ']' '/' 'fiq' ']'").
Notation " 'qif' phi [ x ] 'then' u 'fiq'" := (qcond2_ x phi uskip_ u)
  (in custom cmd at level 20, x custom reg, phi constr,
  format "'[v' 'qif'  phi [ x ]  'then'  '/' '['     u ']' '/' 'fiq' ']'").
Notation t2tv_reverse_coercion := (@reverse_coercion _ _
  (inhabited_t2tv__canonical__quantum_ONB (eval_qtype QBool)) (@t2tv (eval_qtype QBool))).
Notation t2tv_reverse_coercion1 := (@reverse_coercion _ _
  (inhabited_t2tv__canonical__quantum_ONB (@reverse_coercion FinInhabited.type Set
  Datatypes_bool__canonical__inhabited_FinInhabited bool)) 
  (@t2tv (@reverse_coercion FinInhabited.type Set
    Datatypes_bool__canonical__inhabited_FinInhabited bool))).
Notation bvmeas_reverse_coercion1 := (@reverse_coercion _ _
  (basic_def_bvmeas__canonical__quantum_QMeasure 
    (@inhabited_t2tv__canonical__quantum_NormalState (@reverse_coercion FinInhabited.type Set
    Datatypes_bool__canonical__inhabited_FinInhabited bool) true))
  (bvmeas (''false))).
Notation bvmeas_reverse_coercion := (@reverse_coercion _ _
  (basic_def_bvmeas__canonical__quantum_QMeasure 
    (@inhabited_t2tv__canonical__quantum_NormalState (eval_qtype QBool) true))
  (bvmeas (''false))).
Notation "'qif' [ x ] 'then' u1 'else' u0 'fiq'" := (qcond2_ x t2tv_reverse_coercion1 u0 u1)
  (in custom cmd at level 20, x custom reg, only printing,
  format "'[v' 'qif'  [ x ]  'then'  '/' '['     u1 ']' '/' 'else' '/' '['     u0 ']' '/' 'fiq' ']'").
Notation "'qif' [ x ] 'then' u1 'else' u0 'fiq'" := (qcond2_ x t2tv_reverse_coercion u0 u1)
  (in custom cmd at level 20, x custom reg,
  format "'[v' 'qif'  [ x ]  'then'  '/' '['     u1 ']' '/' 'else' '/' '['     u0 ']' '/' 'fiq' ']'").
Notation " 'qif' [ x ] 'then' u 'fiq'" := (qcond2_ x t2tv_reverse_coercion1 uskip_ u)
  (in custom cmd at level 20, x custom reg, only printing,
  format "'[v' 'qif'  [ x ]  'then'  '/' '['     u ']' '/' 'fiq' ']'").
Notation " 'qif' [ x ] 'then' u 'fiq'" := (qcond2_ x t2tv_reverse_coercion uskip_ u)
  (in custom cmd at level 20, x custom reg,
  format "'[v' 'qif'  [ x ]  'then'  '/' '['     u ']' '/' 'fiq' ']'").
Notation " u0 '←' { u } phi [ x ] '→' u1 " := (sequ_ (unitary_ x u) (qcond2_ x phi u0 u1))
  (in custom cmd at level 20, x custom reg, phi constr, u constr,
  format "u0  '←'  { u } phi [ x ]  '→'  u1").
Notation " u0 '←' phi [ x ] { u } '→' u1 " := (sequ_ (qcond2_ x phi u0 u1) (unitary_ x u))
  (in custom cmd at level 20, x custom reg, phi constr, u constr,
  format "u0  '←'  phi [ x ] { u }  '→'  u1").
Notation " u0 '←' phi [ x ] '→' u1 " := (qcond2_ x phi u0 u1)
  (in custom cmd at level 20, x custom reg, phi constr,
  format "u0  '←'  phi [ x ]  '→'  u1").
Notation "phi [ x ] '→' u " := (qcond2_ x phi uskip_ u)
  (in custom cmd at level 20, x custom reg,
  format "phi [ x ]  '→'  u").
Notation " u0 '←' '{{' u '}}' [ x ] '→' u1 " := (sequ_ u (qcond2_ x t2tv_reverse_coercion u0 u1))
  (in custom cmd at level 20, x custom reg, only parsing,
  format "u0  '←'  {{ u }} [ x ]  '→'  u1").
Notation " u0 '←' [ x ] '{{' u '}}' '→' u1 " := (sequ_ (qcond2_ x t2tv_reverse_coercion u0 u1) u)
  (in custom cmd at level 20, x custom reg, only parsing,
  format "u0  '←'  [ x ] {{ u }}  '→'  u1").
Notation " u0 '←' { u } [ x ] '→' u1 " := (sequ_ (unitary_ x u) (qcond2_ x t2tv_reverse_coercion1 u0 u1))
  (in custom cmd at level 20, x custom reg, u constr, only printing,
  format "u0  '←'  { u } [ x ]  '→'  u1").
Notation " u0 '←' { u } [ x ] '→' u1 " := (sequ_ (unitary_ x u) (qcond2_ x t2tv_reverse_coercion u0 u1))
  (in custom cmd at level 20, x custom reg, u constr,
  format "u0  '←'  { u } [ x ]  '→'  u1").
Notation " u0 '←' [ x ] { u } '→' u1 " := (sequ_ (qcond2_ x t2tv_reverse_coercion1 u0 u1) (unitary_ x u))
  (in custom cmd at level 20, x custom reg, u constr, only printing,
  format "u0  '←'  [ x ] { u }  '→'  u1").
Notation " u0 '←' [ x ] { u } '→' u1 " := (sequ_ (qcond2_ x t2tv_reverse_coercion u0 u1) (unitary_ x u))
  (in custom cmd at level 20, x custom reg, u constr,
  format "u0  '←'  [ x ] { u }  '→'  u1").
Notation " u0 '←' [ x ] '→' u1 " := (qcond2_ x t2tv_reverse_coercion1 u0 u1)
  (in custom cmd at level 20, x custom reg, only printing,
  format "u0  '←'  [ x ]  '→'  u1").
Notation " u0 '←' [ x ] '→' u1 " := (qcond2_ x t2tv_reverse_coercion u0 u1)
  (in custom cmd at level 20, x custom reg,
  format "u0  '←'  [ x ]  '→'  u1").
Notation " [ x ] '→' u " := (qcond2_ x t2tv_reverse_coercion1 uskip_ u)
  (in custom cmd at level 20, x custom reg, only printing,
  format "[ x ]  '→'  u").
Notation " [ x ] '→' u " := (qcond2_ x t2tv_reverse_coercion uskip_ u)
  (in custom cmd at level 20, x custom reg,
  format "[ x ]  '→'  u").
Definition if_fun (W : Type) (T : eqType) (i : T) (u v : W) j :=
  if j == i then u else v.
Notation "phi [ x ] '→_(' i ) u " := 
  (qcond_ x phi (if_fun i u uskip_))
  (in custom cmd at level 20, x custom reg, i constr, u constr,
  format "phi [ x ]  '→_(' i )  u").
Notation "[ x ] '→_(' i ) u " := 
  (qcond_ x t2tv_reverse_coercion1 (if_fun i u uskip_))
  (in custom cmd at level 20, x custom reg, i constr, u constr, only printing,
  format "[ x ]  '→_(' i )  u").
Notation "[ x ] '→_(' i ) u " := 
  (qcond_ x t2tv_reverse_coercion (if_fun i u uskip_))
  (in custom cmd at level 20, x custom reg, i constr, u constr,
  format "[ x ]  '→_(' i )  u").

Section ucmd_var.
Local Open Scope fset_scope.

Fixpoint ucmd_vset u : {set mlab} :=
    match u with
    | uskip_ => finset.set0
    | unitary_ _ x _ => mset x
    | sequ_ u1 u2 => ucmd_vset u1 :|: ucmd_vset u2
    | qcond_ _ F x _ fu => mset x :|: \bigcup_(i : F) (ucmd_vset (fu i))
    end.

(* syntactically calculate if quantum register is disjoint from circuit u *)
Fixpoint ucmd_var_disj T (x : qreg T) (u : ucmd_) :=
    match u with
    | uskip_ => true
    | unitary_ _ y _ => disjoint_qreg x y 
    | sequ_ u1 u2 => ucmd_var_disj x u1 && ucmd_var_disj x u2 
    | qcond_ _ F y _ fu => disjoint_qreg x y && [forall i : F, ucmd_var_disj x (fu i)]
    end.

(* x is syntactical disjoint from u -> the quantum systems of x and u are disjoint *)
Lemma ucmd_var_disj_vsetP T (x : qreg T) (u : ucmd_) :
    ucmd_var_disj x u -> [disjoint mset x & ucmd_vset u]%B.
Proof.
elim: u=>/=.
by rewrite disjointX0.
by move=>???; rewrite -disj_setE.
by move=>? IH1 ? IH2 /andP[] /IH1 + /IH2; rewrite disjointXU=>->->.
move=>? y F ? fu IH /andP[] + /forallP Pi.
rewrite disjointXU -disj_setE=>-> /=.
by apply/bigcup_disjoint=>i _; apply/IH/Pi.
Qed.

Fixpoint ucmd_var_basic u : {fset basic_index} :=
  match u with
  | uskip_ => fset0
  | unitary_ _ x _ => x
  | sequ_ u1 u2 => ucmd_var_basic u1 `|` ucmd_var_basic u2
  | qcond_ _ F x _ fu => x `|` \bigcup_i ucmd_var_basic (fu i)
  end.

Lemma ucmd_vset_basic u :
  ucmd_vset u = (\bigcup_(i <- ucmd_var_basic u) (mset_basic_index _ i))%SET.
Proof.
elim: u.
- by rewrite /= big_nil.
- by move=>T x U /=; rewrite -mset_fset_qreg.
- move=>u1 H1 u2 H2 /=; rewrite big_fsetU_idem/= -?H1 -?H2//.
  by exact: finset.setUid.
- move=>T F x M f IH /=; rewrite big_fsetU_idem /=; first by exact: finset.setUid.
  rewrite -mset_fset_qreg; f_equal; under eq_bigr do rewrite IH.
  by rewrite big_fsetUs_idem//; exact: finset.setUid.
Qed.

Lemma ucmd_var_basic_leP u1 u2 : 
  ucmd_var_basic u1 `<=` ucmd_var_basic u2 -> ucmd_vset u1 :<=: ucmd_vset u2.
Proof.
move=>/fsubsetP P; rewrite !ucmd_vset_basic.
apply/bigcups_seqP=>/= i Pi _.
apply/bigcup_sup_seq=>//. by apply/P.
Qed.

Lemma ucmd_var_disjE T (x : qreg T) u : 
  ucmd_var_disj x u = [disjoint x & ucmd_var_basic u]%fset.
Proof.
elim: u=>/=.
- by rewrite fdisjointX0.
- move=>T1 x1 _; apply fdisjoint_qregP.
- by move=>u1 -> u2 ->; rewrite fdisjointXU.
move=>T1 F x1 _ f Pf; rewrite fdisjointXU -fdisjoint_qregP; f_equal.
apply/eqb_iff; split.
by move=>/forallP Pi; apply/bigfcup_disjointP=>i _; rewrite -Pf.
move=>/bigfcup_disjointP Pi; apply/forallP=>i; rewrite Pf.
by apply/Pi; rewrite mem_index_enum.
Qed.

(* syntactically calculate if two circuits are disjoint *)
Fixpoint ucmd_disj (u1 : ucmd_) (u2 : ucmd_) :=
    match u1 with
    | uskip_ => true
    | unitary_ _ y _ => ucmd_var_disj y u2 
    | sequ_ u11 u12 => ucmd_disj u11 u2 && ucmd_disj u12 u2 
    | qcond_ _ F y _ fu => ucmd_var_disj y u2 && [forall i : F, ucmd_disj (fu i) u2]
    end.

(* u1 u2 are syntactical disjoint -> the quantum systems of u1 and u2 are disjoint *)
Lemma ucmd_disj_vsetP (u1 u2 : ucmd_) :
    ucmd_disj u1 u2 -> [disjoint ucmd_vset u1 & ucmd_vset u2]%B.
Proof.
elim: u1.
by rewrite /= disjoint0X.
by move=>T x U /=; exact: ucmd_var_disj_vsetP.
by move=>u0 IH0 u1 IH1 /= =>/andP[] /IH0 P0 /IH1 P1; rewrite disjointUX P0 P1.
move=>T F x M f IH /= =>/andP[] /ucmd_var_disj_vsetP Px /forallP Pi.
rewrite disjointUX Px/= disjoint_sym bigcup_disjoint// =>i _.
by rewrite disjoint_sym IH.
Qed.

(* syntactically calculate if register x contains circuit u *)
Definition ucmd_var_subset T (x : qreg T) (u : ucmd_) :=
  ucmd_var_basic u `<=` x.

(* x is syntactical contains circuit u -> the quantum systems of x contains that of u *)
Lemma ucmd_var_subsetP T (x : qreg T) (u : ucmd_) :
  ucmd_var_subset x u -> ucmd_vset u :<=: mset x.
Proof.
rewrite /ucmd_var_subset=>/fsubsetP P.
rewrite ucmd_vset_basic mset_fset_qreg.
apply/bigcups_seqP=>/= i Pi _.
by apply/bigcup_sup_seq=>//; by apply/P.
Qed.

Lemma ucmd_disjE (u1 : ucmd_) (u2 : ucmd_) :
  ucmd_disj u1 u2 = [disjoint ucmd_var_basic u1 & ucmd_var_basic u2].
Proof.
elim: u1 u2 => /=.
by move=>?; rewrite fdisjoint0X.
by move=>T x U u; rewrite ucmd_var_disjE.
by move=>u1 IH1 u2 IH2 u; rewrite IH1 IH2 fdisjointUX.
move=>T F x _ f IH u; rewrite fdisjointUX ucmd_var_disjE; f_equal.
apply/eqb_iff; split; rewrite fdisjoint_sym.
by move=>/forallP Pi; apply/bigfcup_disjointP=>i _; rewrite fdisjoint_sym -IH.
move=>/bigfcup_disjointP Pi; apply/forallP=>i; rewrite IH fdisjoint_sym.
by apply/Pi; rewrite mem_index_enum.
Qed.

End ucmd_var.

(* ---------------------------------------------------- *)
(* syntactically calculate if a circuit is well-formed  *)
(* 1. skip is wf;                                       *)
(* 2. unitary should act on a valid-qreg;               *)
(* 3. u1 ; u2 is wf if u1 and u2 are both wf            *)
(* 4. qif [y] = i => fc i fiq is wf if                  *) 
(*      (a). y is valid-qreg;                           *)
(*      (b) for all i, fc i is wf;                      *)
(*      (c) for all i, y and fc i are disjoint          *)
(* ---------------------------------------------------- *)
Fixpoint ucmd_wf (u : ucmd_) : bool :=
    match u with
    | uskip_ => true
    | unitary_ _ x _ => valid_qreg x
    | sequ_ u1 u2 => ucmd_wf u1 && ucmd_wf u2
    | qcond_ _ F y _ fc => valid_qreg y && 
        [forall i : F, ucmd_wf (fc i) && ucmd_var_disj y (fc i)]
    end.

(* semantics of circuit; it slightly different from Definition 3.3, *)
Fixpoint usem_aux (u : ucmd_) : 'F[msys]_finset.setT :=
    match u with
    | uskip_ => \1
    | unitary_ T x U => liftf_lf (tf2f x x U)
    | sequ_ u1 u2 => usem_aux u2 \o usem_aux u1
    | qcond_ T F x b fc => \sum_(i : F) (liftf_lf (tf2f x x [> b i ; b i <]) \o
                    usem_aux (fc i) \o liftf_lf (tf2f x x [> b i ; b i <]))
    end.
HB.lock Definition usem := usem_aux.

(* --------------------------------------------------------------- *)
(*                   Definition 3.3 : local semantics              *)
(* We show that if circuit u is well-formed, two definitions are   *)
(* equivalent in the global system,                                *) 
(*   as proved in Lemma usem_equivalent_def below                  *)
(* --------------------------------------------------------------- *)
(* We select to use usem instead of usem_def below is because:     *)
(*    1. they are equivalent, so it's alternative to choose one    *)
(*    2. global semantics is not a dependent type, which           *)
(*       significantly simplified the coq proofs, without annoying *) 
(*       type cast problem                                         *)
(*    3. we carefully define usem to make its behavior reasonably  *) 
(*       good even for not well-formed programs which, although,   *) 
(*       out of our consideration, but will significantly make     *) 
(*       proofs easier (that's why we minimize the premises,       *)
(*       instead of keeping well-formedness everywhere )           *)
(* --------------------------------------------------------------- *)
Fixpoint usem_def (u : ucmd_) : 'F[msys]_(ucmd_vset u) :=
    match u return 'F[msys]_(ucmd_vset u) with
    | uskip_ => \1
    | unitary_ T x U => (tf2f x x U)
    | sequ_ u1 u2 => 
        (lift_lf (finset.subsetUr _ _) (usem_def u2)) \o 
        (lift_lf (finset.subsetUl _ _) (usem_def u1))
    | qcond_ T F x b fc => 
        \sum_(i : F) (tf2f x x [> b i ; b i <] \⊗
            (lift_lf (map_cover _ i) (usem_def (fc i))))
    end.

(* structural representation of usem *)
Lemma usem_skip : usem <{[ uskip ]}> = \1.
Proof. by rewrite usem.unlock. Qed.
Lemma usem_unitary T (x : qreg T) U : usem <{[ [x] *= U ]}> = liftf_lf (tf2f x x U).
Proof. by rewrite usem.unlock. Qed.
Lemma usem_sequ u1 u2 : usem <{[ u1; u2 ]}> = usem u2 \o usem u1.
Proof. by rewrite usem.unlock. Qed.
Lemma usem_qcond T (F : finType) (x : qreg T) b (f : F -> ucmd_) :
  usem <{[ qif b[x] = i then f i fiq ]}> = 
    \sum_(i : F) (liftf_lf (tf2f x x [> b i ; b i <]) \o
                    usem (f i) \o liftf_lf (tf2f x x [> b i ; b i <])).
Proof. by rewrite usem.unlock. Qed.
Lemma usem_qcond2 x b c0 c1 :
  usem <{[ c0 ← b[x] → c1 ]}> = 
    (liftf_lf (tf2f x x [> b true ; b true <]) \o usem c1 \o liftf_lf (tf2f x x [> b true ; b true <]))
    + (liftf_lf (tf2f x x [> b false ; b false <]) \o usem c0 \o liftf_lf (tf2f x x [> b false ; b false <])).
Proof. by rewrite qcond2_.unlock usem_qcond big_bool/=. Qed.
Definition usemE := (usem_skip, usem_unitary, usem_sequ, usem_qcond, usem_qcond2).

Lemma usem_local u : exists U : 'F_(ucmd_vset u), usem u = liftf_lf U.
Proof.
elim: u=>/=.
- by exists \1; rewrite usemE liftf_lf1.
- by move=>T x U; exists (tf2f x x U); rewrite usemE.
- move=>u1 [U1 PU1] u2 [U2 PU2].
  exists ((lift_lf (finset.subsetUr _ _) U2) \o (lift_lf (finset.subsetUl _ _) U1)).
  by rewrite usemE PU1 PU2 liftf_lf_comp/= !liftf_lf2.
- move=>T F x t u IH.
pose ui i : 'F_(\bigcup_i ucmd_vset (u i)) := 
  lift_lf (finset.bigcup_sup i is_true_true) (projT1 (cid (IH i))).
have P3i i : usem (u i) = liftf_lf (ui i)
  by rewrite /ui liftf_lf2; move: (projT2 (cid (IH i))).
exists (\sum_i (lift_lf (finset.subsetUl _ _) (tf2f x x [> t i ; t i <]) \o 
  (lift_lf (finset.subsetUr _ _) (ui i)) \o lift_lf (finset.subsetUl _ _) (tf2f x x [> t i ; t i <]))).
rewrite usemE linear_sum/=; apply eq_bigr=>i _.
by rewrite P3i !liftf_lf_comp !liftf_lf2.
Qed.

(* we show that for well-formed circuit, two definitions are equivalent *)
(* liftf_lf is the cylindrical extension to the global system, i.e.,    *)
(* liftf_lf u = u \⊗ I, and dealing with an additional type cast       *)
Lemma usem_equivalent_def u :
  ucmd_wf u -> usem u = liftf_lf (usem_def u).
Proof.
elim: u.
by rewrite usemE /= liftf_lf1.
by move=>T x U _; rewrite usemE.
by move=>u1 IH1 u2 IH2 /=/andP[] /IH1 H1 /IH2 H2; 
  rewrite usemE H1 H2 liftf_lf_comp !liftf_lf2.
move=>T F x M u IH /= /andP[] Px /forallP Pi.
rewrite usemE linear_sum/=; apply eq_bigr=>i _.
move: (Pi i)=>/andP[] wi /ucmd_var_disj_vsetP di.
rewrite IH// liftf_lf_compC// -comp_lfunA -liftf_lf_comp tf2f_comp outp_comp 
  ns_dot scale1r -liftf_lf_compC// -liftf_lf_compT// ?liftf_lf2//.
by apply bigcup_disjoint=>j _; move: (Pi j)=>/andP[] _ /ucmd_var_disj_vsetP.
Qed.

Lemma ucmd_wf_usem u {PU : ucmd_wf u} :
    exists U : 'FU_(ucmd_vset u), usem u = liftf_lf U.
Proof.
elim: u PU =>/=.
- by move=>_; exists \1; rewrite usemE liftf_lf1.
- by move=>T x U; rewrite /cmd_expose=>Px; exists (tf2f x x U); rewrite usemE.
- move=>u1 IH1 u2 IH2 /andP[] /IH1 [U1 PU1] /IH2 [U2 PU2].
  exists ((lift_lf (finset.subsetUr _ _) U2) \o (lift_lf (finset.subsetUl _ _) U1)).
  by rewrite usemE PU1 PU2 liftf_lf_comp/= !liftf_lf2.
- move=>T F x t u IH /andP[] Px /forallP Pi.
have P1i i : ucmd_wf (u i) by move: (Pi i)=>/andP[].
have P2i i : ucmd_var_disj x (u i) by move: (Pi i)=>/andP[].
pose ui i : 'F_(\bigcup_i ucmd_vset (u i)) := 
  lift_lf (finset.bigcup_sup i is_true_true) (projT1 (cid (IH i (P1i i)))).
have P3i i : usem (u i) = liftf_lf (ui i)
  by rewrite /ui liftf_lf2; move: (projT2 (cid (IH i (P1i i)))).
pose U : 'F__ := \sum_i (tf2f x x [> t i ; t i <] \⊗ (ui i)).
have Pd : [disjoint mset x & \bigcup_i ucmd_vset (u i)]
  by apply/bigcup_disjoint=>i _; apply/ucmd_var_disj_vsetP/P2i.
have UU : U \is unitarylf.
rewrite unitarylfE /U adjf_sum linear_sumr/= -tenf11 
  -(sumonb_out (tv2v_fun _ x t)) /tv2v_fun/=/tv2v_fun linear_suml/=.
apply/eqP; apply eq_bigr=>i _.
rewrite linear_suml/= [LHS](bigD1 i)//= [X in _ + X]big1.
by move=>j /negPf nji; rewrite tenf_adj -tenf_comp// tf2f_adj 
  tf2f_comp adj_outp outp_comp onb_dot nji scale0r linear0 linear0l.
by rewrite tenf_adj -tenf_comp// tf2f_adj tf2f_comp unitaryfEl 
  adj_outp outp_comp onb_dot eqxx scale1r addr0 tv2v_out.
exists (UnitaryLf_Build UU)=>/=; rewrite /U linear_sum/= usemE.
by apply eq_bigr=>i _; rewrite P3i liftf_lf_compT// -(liftf_lf_tenf1r _ Pd) 
  -liftf_lf_comp -tenf_comp// comp_lfun1r tf2f_comp outp_comp onb_dot eqxx scale1r.
Qed.

Lemma usem_wf_unitary u {PU : ucmd_wf u} :
  usem u \is unitarylf.
Proof. move: (@ucmd_wf_usem u PU)=>[] U ->; apply/is_unitarylf. Qed.

Lemma usem_bound1 u : usem u \is bound1lf.
Proof.
rewrite bound1lf_form_le1.
elim: u=>/=; rewrite usem.unlock.
- by rewrite /= adjf1 comp_lfun1l.
- move=>T x U; rewrite -liftf_lf_adj -liftf_lf_comp tf2f_adj -liftf_lf_le1.
  rewrite !tf2f_UE. apply/lef_dot=>v.
  by rewrite lfunE/= -adj_dotEl !adjf_comp !adjfK [\1 v]lfunE/= comp_lfunA bound1f_dot.
- move=>u1 IH1 u2 IH2.
  rewrite adjf_comp !comp_lfunA comp_lfunACA.
  apply: (le_trans _ IH1); rewrite -{2}[(usem_aux u1)^A]comp_lfun1r.
  by apply/lef_form.
move=>? x F t fu IH.
have Pi i : usem_aux (fu i) \is bound1lf by rewrite bound1lf_form_le1.
pose ft i := [> t i ; t i <].
have Pft : trace_nincr ft.
  by rewrite /trace_nincr -(sumonb_out t) lev_sum// =>i _; 
    rewrite /ft adj_outp outp_comp onb_dot eqxx scale1r.
rewrite -bound1lf_form_le1 /=.
under eq_bigr do rewrite -{2}adj_outp -tf2f_adj liftf_lf_adj -formlfE 
  tf2f_UE (Bound1Lf_BuildE (Pi _)) -/(ft _) (TraceNincr_BuildE Pft).
apply: formlf_liftf_sum_bound1.
by move=>i j /negPf nij; rewrite /= adj_outp outp_comp onb_dot nij scale0r.
rewrite -(sumonb_out t) lev_sum=>[i _|//];
by rewrite /= adj_outp outp_comp onb_dot eqxx scale1r lexx.
Qed.
HB.instance Definition _ u := isBound1Lf.Build _ _ _ (usem_bound1 u).
(* HB fails here if we infer PU from typeclass_instance *)
Canonical usem_isofType u {PU} := IsoLf_Build (unitarylf_iso (@usem_wf_unitary u PU)).
Canonical usem_gisofType u {PU} := GisoLf_Build (unitarylf_giso (@usem_wf_unitary u PU)).
Canonical usem_normalfType u {PU} := NormalLf.copy (usem u) (@usem_gisofType u PU).

Lemma usem_big I (r : seq I) (P : pred I) (f : I -> ucmd_) :
  usem (\big[sequ_/uskip_]_(i <- r | P i) f i) = 
    \big[ (fun i j => comp_lfun j i) / \1 ]_(i <- r | P i) usem (f i).
Proof.
elim/big_rec2: _; first by rewrite usemE.
by move=>i y1 y2 _ <-; rewrite usemE.
Qed.

Lemma ucmd_var_basic_big I (r : seq I) (P : pred I) (f : I -> ucmd_) :
  ucmd_var_basic (\big[sequ_/uskip_]_(i <- r | P i) (f i)) = 
    (\bigcup_(i <- r | P i) ucmd_var_basic (f i))%fset.
Proof. by elim/big_rec2: _=>// i y1 y2 Pi /= <-. Qed.

(* alternative definition of Definition 4.1 *)
HB.lock
Definition eq_usem u1 u2 := usem u1 = usem u2.
Notation "u1 '=u' u2" := (eq_usem u1 u2) 
  (at level 70, format "'[hv' '[ ' u1 ']'  '/' '=u'  '/' '[ ' u2 ']' ']'").

(* we show that for well-formed circuit u1 u2,                         *)
(*    u1 =u u2 is equivalent to the Definition 4.1                     *)
(* lift_lf is the cylindrical extension to the larger system, i.e.,    *)
(* lift_lf _ u = u \⊗ I, and dealing with an additional type cast     *)
Lemma eq_usem_alternative u1 u2 : 
  ucmd_wf u1 -> ucmd_wf u2 ->
    u1 =u u2 <->
      (lift_lf (finset.subsetUl _ _) (usem_def u1) = 
       lift_lf (finset.subsetUr _ _) (usem_def u2)).
Proof.
move=>P1 P2; split; rewrite eq_usem.unlock !usem_equivalent_def//.
by move=>H; apply/liftf_lf_inj; rewrite !liftf_lf2.
by move=>/(f_equal (fun x => liftf_lf x)); rewrite !liftf_lf2.
Qed.

Lemma eq_usem_trans : 
  forall a b c, a =u b -> b =u c -> a =u c.
Proof. by rewrite eq_usem.unlock; move=>a b c -> ->. Qed.
Lemma eq_usem_refl : forall a, a =u a.
Proof. by rewrite eq_usem.unlock. Qed.
Lemma eq_usem_sym : forall a b, a =u b -> b =u a.
Proof. by rewrite eq_usem.unlock; move=>a b ->. Qed.
Hint Extern 0 (eq_usem _ _) => (apply eq_usem_refl) : core.

Lemma eq_usemE (u1 u2 : ucmd_) : u1 =u u2 -> (usem u1 = usem u2).
Proof. by rewrite eq_usem.unlock. Qed.

Add Parametric Relation : ucmd_ eq_usem
  reflexivity proved by eq_usem_refl
  symmetry proved by eq_usem_sym
  transitivity proved by eq_usem_trans
  as eq_usem_rel.

(* enable setoid rewriting for =u *)
Module Export EQ_USEM.
Require Import Setoid.

Add Parametric Morphism : sequ_
  with signature eq_usem ==> eq_usem ==> eq_usem as eq_usem_sequ.
Proof. by rewrite eq_usem.unlock=>??+??+; rewrite !usemE=>->->. Qed.

Add Parametric Morphism (T : qType) : (@unitary_ T)
  with signature (@eq_qreg T) ==> (@eq _) ==> eq_usem as eq_usem_unitary.
Proof.
by move=>x y Pxy U; rewrite eq_usem.unlock !usemE -(tf2f_eqr _ Pxy Pxy) liftf_lf_cast.
Qed.

Add Parametric Morphism (T : qType) (F : finType) : (@qcond_ T F)
  with signature (@eq_qreg T) ==> (@eq _) ==> (@eq _) ==> eq_usem as eq_usem_qcond.
Proof.
move=>x y Pxy M f; rewrite eq_usem.unlock !usemE.
by apply eq_bigr=>i _; rewrite -(tf2f_eqr _ Pxy Pxy) liftf_lf_cast.
Qed.

Add Parametric Morphism : qcond2_ with
  signature (@eq_qreg Bool) ==> (@eq _) ==> 
    eq_usem ==> eq_usem ==> eq_usem as eq_usem_qcond2.
Proof.
move=>x y Pxy M c00 c01 + c10 c11 +.
by rewrite eq_usem.unlock !usemE -!(tf2f_eqr _ Pxy Pxy) !liftf_lf_cast=>->->.
Qed.

Lemma eq_onb (U : chsType) (F : finType) (M1 M2 : 'ONB(F; U)) :
  (forall i, M1 i = M2 i) <-> M1 = M2.
Proof.
split=>[/funext|->//].
case: M1=>f1 [][] P11 [] P12; case: M2=>f2 [][] P21 [] P22/= P.
case: _ / P P21 P22 => P21 P22.
by rewrite (Prop_irrelevance P11 P21) (eq_irrelevance P12 P22).
Qed.

Lemma eq_ponb (U : chsType) (F : finType) (M1 M2 : 'PONB(F; U)) :
  (forall i, M1 i = M2 i) <-> M1 = M2.
Proof.
split=>[/funext|->//].
case: M1=>f1 [][] P1; case: M2=>f2 [][] P2 /= P.
case: _ / P P2 => P2.
by rewrite (Prop_irrelevance P1 P2).
Qed.

Lemma eq_qcond (T : qType) (x : qreg T) (F : finType) (M1 M2 : 'ONB(F; 'Ht T))
  (f1 f2 : F -> ucmd_) :
  (forall i, M1 i = M2 i) -> (forall i, f1 i =u f2 i) -> 
  <{[ qif M1[x] = i then f1 i fiq ]}> =u <{[ qif M2[x] = i then f2 i fiq ]}>.
Proof. 
rewrite eq_usem.unlock=>PM Pf; rewrite !usemE; under eq_bigr do rewrite Pf.
by apply eq_bigr=>i _; do ! f_equal; apply/eq_onb.
Qed.

Lemma eq_qcondl (T : qType) (x : qreg T) (F : finType) (M1 M2 : 'ONB(F; 'Ht T))
  (f : F -> ucmd_) :
  (forall i, M1 i = M2 i) -> 
    <{[ qif M1[x] = i then f i fiq ]}> =u <{[ qif M2[x] = i then f i fiq ]}>.
Proof. by move=>/eq_qcond; apply. Qed.

Lemma eq_qcondr (T : qType) (x : qreg T) (F : finType) (M : 'ONB(F; 'Ht T))
  (f1 f2 : F -> ucmd_) :
  (forall i, f1 i =u f2 i) -> 
  <{[ qif M[x] = i then f1 i fiq ]}> =u <{[ qif M[x] = i then f2 i fiq ]}>.
Proof. by move=>/eq_qcond; apply. Qed.

Lemma eq_qcond2 (x : qreg Bool) (M1 M2 : 'ONB) c0 c1 :
  (forall i, M1 i = M2 i) -> 
  <{[ c0 ← M1[x] → c1 ]}> =u <{[ c0 ← M2[x] → c1 ]}>.
Proof. by rewrite qcond2_.unlock=>/eq_qcondl; apply. Qed.

Lemma eq_unitary (T : qType) (x : qreg T) (U1 U2 : 'FU('Ht T)) :
  U1 = U2 :> 'End(_) -> <{[ [x] *= U1 ]}> =u <{[ [x] *= U2 ]}>.
Proof. by rewrite eq_usem.unlock !usemE/==>->. Qed.

Lemma eq_bigr_usem I (r : seq I) (P : pred I) (f g : I -> ucmd_) :
  (forall i, P i -> f i =u g i) ->
    \big[sequ_/uskip_]_(i <- r | P i) f i =u \big[sequ_/uskip_]_(i <- r | P i) g i.
Proof. by move=>Pi; elim/big_rec2: _=>// j y1 y2 /Pi -> ->. Qed.

End EQ_USEM.

Section CircuitLaws.

(* proposition 4.1 (1) : quantum if-statement, changing basis *)
Lemma qif_change_basisG T F (q : 'QReg[T]) (psi phi : 'ONB(F;'Ht T)) 
  (c : F -> ucmd_) {H : `{{forall i, (ucmd_var_disj q (c i))}}} :
  <{[ qif psi[q] = i then c i fiq ]}> =u 
    <{[ ([q] *= onb_change psi phi) ; (qif phi[q] = i then c i fiq) ; ([q] *= onb_change phi psi) ]}>.
Proof.
rewrite eq_usem.unlock !usemE linear_suml/= linear_sumr/=; apply eq_bigr=>i _.
move: (H i)=>/ucmd_var_disj_vsetP Hi.
move: (usem_local (c i))=>[U ->].
rewrite !comp_lfunA -liftf_lf_comp ![_ \o liftf_lf U]liftf_lf_compC// -!comp_lfunA; f_equal.
by rewrite -!liftf_lf_comp !tf2f_comp !outp_compr onb_changeE !outp_compl 
  onb_change_adj onb_changeE adj_outp !outpE !onb_dot !eqxx scale1r.
Qed.

Lemma qif_change_basisGP T F (q : 'QReg[T]) (psi phi : 'ONB(F;'Ht T)) 
  (c : F -> ucmd_) (Ul Ur : 'FU) {H : `{{forall i, (ucmd_var_disj q (c i))}}} :
  Ul = onb_change psi phi :> 'End(_) -> Ur = onb_change phi psi :> 'End(_) ->
  <{[ qif psi[q] = i then c i fiq ]}> =u 
    <{[ ([q] *= Ul) ; (qif phi[q] = i then c i fiq) ; ([q] *= Ur) ]}>.
Proof.
by move=>Pl Pr; rewrite (eq_unitary _ Pl)/= (eq_unitary _ Pr) -qif_change_basisG.
Qed.

Lemma qif_change_basis (q : qreg Bool) (psi : 'ONB) (phi : 'ONB) c0 c1 
  {H0 : `{{ucmd_var_disj q c0}}} {H1 : `{{ucmd_var_disj q c1}}} :
  <{[ c0 ← psi[q] → c1 ]}> =u 
    <{[ ([q] *= onb_change psi phi); (c0 ← phi[q] → c1) ; ([q] *= onb_change phi psi) ]}>.
Proof.
have H : `{{forall i, (ucmd_var_disj q (if i then c1 else c0))}} by case.
by rewrite qcond2_.unlock (qif_change_basisG _ phi).
Qed.

Lemma qif_change_basisP (q : qreg Bool) (psi : 'ONB) (phi : 'ONB) c0 c1 
  {H0 : `{{ucmd_var_disj q c0}}} (Ul Ur : 'FU) {H1 : `{{ucmd_var_disj q c1}}} :
  Ul = onb_change psi phi :> 'End(_) -> Ur = onb_change phi psi :> 'End(_) ->
  <{[ c0 ← psi[q] → c1 ]}> =u 
    <{[ ([q] *= Ul); (c0 ← phi[q] → c1) ; ([q] *= Ur) ]}>.
Proof.
by move=>Pl Pr; rewrite (eq_unitary _ Pl)/= (eq_unitary _ Pr) -qif_change_basis.
Qed.

(* proposition 4.1 (2) : quantum if-statement, symmetry *)
Lemma qif_sym (q : qreg Bool) (phi : 'ONB) c0 c1 :
  <{[ c0 ← phi[q] → c1 ]}> =u <{[ c1 ← (onb_swap phi)[q] → c0 ]}>.
Proof. by rewrite eq_usem.unlock !usemE/= /onb_swap/= addrC. Qed.

Lemma qif_symP (q : qreg Bool) (phi psi : 'ONB) c0 c1 :
  (forall i, psi i = (onb_swap phi) i) ->
  <{[ c0 ← phi[q] → c1 ]}> =u <{[ c1 ← psi[q] → c0 ]}>.
Proof. by move=>/eq_qcond2->; exact: qif_sym. Qed.

(* proposition 4.1 (3) : quantum if-statement, idempotence *)
Lemma qif_idemG T F (q : 'QReg[T]) (phi : 'ONB(F; 'Ht T)) c 
  {H0 : `{{ucmd_var_disj q c}}} :
  <{[ qif phi[q] = i then c fiq ]}> =u c.
Proof.
move: H0 => /ucmd_var_disj_vsetP H0; rewrite eq_usem.unlock usemE.
move: (usem_local c)=>[U ->].
under eq_bigr do rewrite ![_ \o liftf_lf U]liftf_lf_compC// -!comp_lfunA
   -liftf_lf_comp/= tf2f_comp !outp_comp !ns_dot !scale1r.
by rewrite -linear_sumr/= -!linear_sum/= sumonb_out tf2f1 liftf_lf1 comp_lfun1r.
Qed.

Lemma qif_idemB (q : qreg Bool) phi c {H0 : `{{ucmd_var_disj q c}}} :
  <{[ c ← phi[q] → c ]}> =u c.
Proof.
rewrite qcond2_.unlock. under eq_qcondr do rewrite if_same.
by rewrite qif_idemG.
Qed.

Lemma qif_idem (q : qreg Bool) c {H0 : `{{ucmd_var_disj q c}}} :
  <{[ c ← [q] → c ]}> =u c.
Proof. exact: qif_idemB. Qed.

(* proposition 4.1 (4) : quantum if-statement, distributivity *)
Lemma qif_distrrB (q1 q2 : qreg Bool) phi psi c c0 c1 
  {H0 : `{{disjoint_qreg q1 q2}}} {H1 : `{{ucmd_var_disj q2 c}}} :
  <{[ c ← phi[q1] → (c0 ← psi[q2] → c1) ]}> =u 
    <{[ (c ← phi[q1] → c0) ← psi[q2] → (c ← phi[q1] → c1) ]}>.
Proof.
move: H0 H1; rewrite (disj_setE default_qmemory)=>H0 /ucmd_var_disj_vsetP H1.
rewrite eq_usem.unlock !usemE !linearDr/= !linearDl/=.
set u11 := liftf_lf _. set u21 := liftf_lf _. set u20 := liftf_lf _.
set u10 := liftf_lf _.
rewrite addrACA; do 2 f_equal.
1,2: rewrite !comp_lfunA liftf_lf_compC// -!comp_lfunA -liftf_lf_compC//.
move: (usem_local c)=>[U ->].
set u1 := (u10 \o liftf_lf U) \o u10.
suff ->: u21 \o u1 = u1 \o u21.
suff ->: u20 \o u1 = u1 \o u20.
rewrite -comp_lfunA -[X in _ + X]comp_lfunA -linearDr/=.
by rewrite /u21 /u20 -!liftf_lf_comp !tf2f_comp !outp_comp !onb_dot !eqxx 
  !scale1r -!linearD/= sumonb_out_bool tf2f1 liftf_lf1 comp_lfun1r.
all: rewrite /u1 !comp_lfunA -liftf_lf_compC// -!comp_lfunA; f_equal;
  rewrite comp_lfunA liftf_lf_compC// -comp_lfunA -liftf_lf_compC//.
Qed.

Lemma qif_distrr (q1 q2 : qreg Bool) c c0 c1 
  {H0 : `{{disjoint_qreg q1 q2}}} {H1 : `{{ucmd_var_disj q2 c}}} :
  <{[ c ← [q1] → (c0 ← [q2] → c1) ]}> =u 
    <{[ (c ← [q1] → c0) ← [q2] → (c ← [q1] → c1) ]}>.
Proof. exact: qif_distrrB. Qed.

Lemma qif_distrlB (q1 q2 : qreg Bool) phi psi c c0 c1 
  {H0 : `{{disjoint_qreg q1 q2}}}
  {H1 : `{{ucmd_var_disj q2 c}}} :
  <{[ (c0 ← psi[q2] → c1) ← phi[q1] → c ]}> =u 
    <{[ (c0 ← phi[q1] → c) ← psi[q2] → (c1 ← phi[q1] → c) ]}>.
Proof.
move: H0 H1; rewrite (disj_setE default_qmemory)=>H0 /ucmd_var_disj_vsetP H1.
rewrite eq_usem.unlock !usemE !linearDr/= !linearDl/=.
set u11 := liftf_lf _. set u10 := liftf_lf _. set u21 := liftf_lf _.
set u20 := liftf_lf _.
rewrite addrACA; do 2 f_equal.
2,3: rewrite !comp_lfunA liftf_lf_compC// -!comp_lfunA -liftf_lf_compC//.
move: (usem_local c)=>[U ->].
set u1 := (u11 \o liftf_lf U) \o u11.
suff ->: u21 \o u1 = u1 \o u21.
suff ->: u20 \o u1 = u1 \o u20.
rewrite -comp_lfunA -[X in _ + X]comp_lfunA -linearDr/=.
by rewrite /u21 /u20 -!liftf_lf_comp !tf2f_comp !outp_comp !onb_dot !eqxx 
  !scale1r -!linearD/= sumonb_out_bool tf2f1 liftf_lf1 comp_lfun1r.
all: rewrite /u1 !comp_lfunA -liftf_lf_compC// -!comp_lfunA; f_equal;
  rewrite comp_lfunA liftf_lf_compC// -comp_lfunA -liftf_lf_compC//.
Qed.

Lemma qif_distrl (q1 q2 : qreg Bool) c c0 c1 
  {H0 : `{{disjoint_qreg q1 q2}}}
  {H1 : `{{ucmd_var_disj q2 c}}} :
  <{[ (c0 ← [q2] → c1) ← [q1] → c ]}> =u 
    <{[ (c0 ← [q1] → c) ← [q2] → (c1 ← [q1] → c) ]}>.
Proof. exact: qif_distrlB. Qed.

(* proposition 4.1 (5) : quantum if-statement, nested-qif *)
Lemma qif_nestrGB T1 T2 (q1 : 'QReg[T1]) (q2 : 'QReg[T2]) (F1 F2 : finType)
  (phi1 : 'ONB(F1; 'Ht T1)) (phi2 : 'ONB(F2; 'Ht T2)) 
  (c : F1 -> F2 -> ucmd_) {H0 : `{{disjoint_qreg q1 q2}}} :
  <{[ qif phi2[q2] = i2 then <{[ qif phi1[q1] = i1 then c i1 i2 fiq ]}> fiq ]}> =u 
  <{[ qif tentv_onbasis phi1 phi2[(q1, q2)] = i then c i.1 i.2 fiq ]}>.
Proof.
rewrite eq_usem.unlock !usemE.
under eq_bigr do rewrite usemE linear_sumr/= linear_suml/=.
rewrite exchange_big pair_big/=. apply eq_bigr=>[[i j]] _.
rewrite /tentv_fun/= !comp_lfunA -comp_lfunA; do 2 f_equal.
by rewrite -tentv_out -tf2f_pair -tenf_castC !liftf_lf_cast -liftf_lf_compT// disjoint_sym -disj_setE.
by rewrite -tentv_out -tf2f_pair !liftf_lf_cast -liftf_lf_compT// -disj_setE.
Qed.

Lemma qif_nestrG T1 T2 (q1 : 'QReg[T1]) (q2 : 'QReg[T2]) 
  (c : evalQT T1 -> evalQT T2 -> ucmd_) {H0 : `{{disjoint_qreg q1 q2}}} :
  <{[ qif [q2] = i2 then <{[ qif [q1] = i1 then c i1 i2 fiq ]}> fiq ]}> =u 
  <{[ qif [(q1, q2)] = i then c i.1 i.2 fiq ]}>.
Proof. by rewrite qif_nestrGB; apply: eq_qcondl=>/=[[]]i1 i2; rewrite /tentv_fun tentv_t2tv. Qed.

Lemma qif_nestlGB T1 T2 (q1 : 'QReg[T1]) (q2 : 'QReg[T2]) (F1 F2 : finType)
  (phi1 : 'ONB(F1; 'Ht T1)) (phi2 : 'ONB(F2; 'Ht T2)) 
  (c : F1 -> F2 -> ucmd_) {H0 : `{{disjoint_qreg q1 q2}}} :
  <{[ qif phi1[q1] = i1 then <{[ qif phi2[q2] = i2 then c i1 i2 fiq ]}> fiq ]}> =u 
  <{[ qif tentv_onbasis phi1 phi2[(q1, q2)] = i then c i.1 i.2 fiq ]}>.
Proof.
rewrite eq_usem.unlock !usemE.
under eq_bigr do rewrite usemE linear_sumr/= linear_suml/=.
rewrite pair_big/=. apply eq_bigr=>[[i j]] _.
rewrite /tentv_fun/= !comp_lfunA -comp_lfunA; do 2 f_equal.
by rewrite -tentv_out -tf2f_pair !liftf_lf_cast -liftf_lf_compT// -disj_setE.
by rewrite -tentv_out -tf2f_pair -tenf_castC !liftf_lf_cast -liftf_lf_compT// disjoint_sym -disj_setE.
Qed.

Lemma qif_nestlG T1 T2 (q1 : 'QReg[T1]) (q2 : 'QReg[T2]) 
  (c : evalQT T1 -> evalQT T2 -> ucmd_) {H0 : `{{disjoint_qreg q1 q2}}} :
  <{[ qif [q1] = i1 then <{[ qif [q2] = i2 then c i1 i2 fiq ]}> fiq ]}> =u 
  <{[ qif [(q1, q2)] = i then c i.1 i.2 fiq ]}>.
Proof. by rewrite qif_nestlGB; apply: eq_qcondl=>/=[[]]i1 i2; rewrite /tentv_fun tentv_t2tv. Qed.

Lemma qif_nestrB (q1 q2 : qreg Bool) phi1 phi2 c00 c01 c10 c11
  {H0 : `{{disjoint_qreg q1 q2}}} :
  <{[ (c00 ← phi1[q1] → c01) ← phi2[q2] → (c10 ← phi1[q1] → c11) ]}> =u
    <{[ qif tentv_onbasis phi1 phi2[(q1, q2)] = i then 
      if i.1 then if i.2 then c11 else c01 else if i.2 then c10 else c00 fiq ]}>.
Proof.
rewrite qcond2_.unlock.
pose c := fun i j => if i then (if j then c11 else c01) else (if j then c10 else c00).
have ->: (fun i => if i.1 then (if i.2 then c11 else c01) else (if i.2 then c10 else c00)) = 
  (fun i => c i.1 i.2) by apply/funext=>[[i j]].
rewrite -qif_nestrGB//.
apply: eq_qcondr; case=>/=; apply: eq_qcondr; case=>//=.
Qed.

Lemma qif_nestr (q1 q2 : qreg Bool) c00 c01 c10 c11
  {H0 : `{{disjoint_qreg q1 q2}}} :
  <{[ (c00 ← [q1] → c01) ← [q2] → (c10 ← [q1] → c11) ]}> =u
    <{[ qif [(q1, q2)] = i then 
      (if i.1 then if i.2 then c11 else c01 else if i.2 then c10 else c00) fiq ]}>.
Proof.
by rewrite qif_nestrB/=; apply: eq_qcondl=>/=[[]]i1 i2; rewrite /tentv_fun tentv_t2tv.
Qed.

Lemma qif_nestlB (q1 q2 : qreg Bool) phi1 phi2 c00 c01 c10 c11
  {H0 : `{{disjoint_qreg q1 q2}}} :
  <{[ (c00 ← phi2[q2] → c10) ← phi1[q1] → (c01 ← phi2[q2] → c11) ]}> =u
    <{[ qif tentv_onbasis phi1 phi2[(q1, q2)] = i then 
      if i.1 then if i.2 then c11 else c01 else if i.2 then c10 else c00 fiq ]}>.
Proof.
rewrite qcond2_.unlock.
pose c := fun i j => if i then (if j then c11 else c01) else (if j then c10 else c00).
have ->: (fun i => if i.1 then (if i.2 then c11 else c01) else (if i.2 then c10 else c00)) = 
  (fun i => c i.1 i.2) by apply/funext=>[[i j]].
rewrite -qif_nestlGB//.
apply: eq_qcondr; case=>/=; apply: eq_qcondr; case=>//=.
Qed.

Lemma qif_nestl (q1 q2 : qreg Bool) c00 c01 c10 c11
  {H0 : `{{disjoint_qreg q1 q2}}} :
  <{[ (c00 ← [q2] → c10) ← [q1] → (c01 ← [q2] → c11) ]}> =u
    <{[ qif [(q1, q2)] = i then 
      (if i.1 then if i.2 then c11 else c01 else if i.2 then c10 else c00) fiq ]}>.
Proof.
by rewrite qif_nestlB/=; apply: eq_qcondl=>/=[[]]i1 i2; rewrite /tentv_fun tentv_t2tv.
Qed.

(* proposition 4.2 (1) : sequential composition, unit *)
Lemma uskipIx u : <{[ uskip ; u ]}> =u <{[ u ]}>.
Proof. by rewrite eq_usem.unlock !usemE comp_lfun1r. Qed.

Lemma uskipxI u : <{[ u ; uskip ]}> =u <{[ u ]}>.
Proof. by rewrite eq_usem.unlock !usemE comp_lfun1l. Qed.

Lemma uskipIid : <{[ uskip ; uskip ]}> =u <{[ uskip ]}>.
Proof. by rewrite uskipIx. Qed.

(* proposition 4.2 (2) : sequential composition, identity *)
Lemma uskip_eq T (x : 'QReg[T]) : 
  <{[ [x] *= \1 ]}> =u <{[ uskip ]}>.
Proof. by rewrite eq_usem.unlock !usemE tf2f1 liftf_lf1. Qed.

Lemma uskip_eqP T (x : 'QReg[T]) (U : 'FU) : 
  U = \1 :> 'End(_) -> <{[ [x] *= U ]}> =u <{[ uskip ]}>.
Proof. by rewrite -(uskip_eq x); apply eq_unitary. Qed.

(* proposition 4.2 (3) : sequential composition, sequential composition *)
Lemma unit_sequ T (x : 'QReg[T]) U1 U2 : 
  <{[ ([x] *= U1) ; ([x] *= U2) ]}> =u <{[ [x] *= U2 \o U1 ]}>.
Proof. by rewrite eq_usem.unlock !usemE/= -liftf_lf_comp tf2f_comp. Qed.

(* proposition 4.2 (4) : sequential composition, parallel composition *)
Lemma unit_sequC T1 T2 (q : qreg T1) (r : qreg T2) U1 U2 
  {H : `{{disjoint_qreg q r}}} :
  <{[ ([q] *= U1) ; ([r] *= U2) ]}> =u <{[ ([r] *= U2) ; ([q] *= U1) ]}>.
Proof. by rewrite eq_usem.unlock !usemE liftf_lf_compC// disjoint_sym -disj_setE. Qed.

Lemma unit_sequT T1 T2 (q : qreg T1) (r : qreg T2) U1 U2 
  {H : `{{disjoint_qreg q r}}} :
  <{[ ([q] *= U1) ; ([r] *= U2) ]}> =u <{[ [(q, r)] *= U1 ⊗f U2 ]}>.
Proof.
by rewrite eq_usem.unlock !usemE -tf2f_pair -tenf_castC 
  !liftf_lf_cast liftf_lf_compT// disjoint_sym -disj_setE.
Qed.

(* proposition 4.2 (5) : sequential composition, commutativity *)
Lemma sequC u1 u2 {H : `{{ucmd_disj u1 u2}}} :
  <{[ u1 ; u2 ]}> =u <{[ u2 ; u1 ]}>.
Proof.
rewrite eq_usem.unlock !usemE.
move: (usem_local u1) (usem_local u2)=>[x1 ->] [x2 ->].
by rewrite liftf_lf_compC// disjoint_sym; apply/ucmd_disj_vsetP.
Qed.

(* proposition 4.2 (6) : sequential composition, associativity *)
Lemma sequA u1 u2 u3 : 
  <{[ u1 ; u2 ; u3 ]}> =u <{[ u1 ; (u2 ; u3) ]}>.
Proof. by rewrite eq_usem.unlock !usemE comp_lfunA. Qed.

(* proposition 4.2 (7) : sequential composition, sequentiality *)
Lemma qif_sequG T (q : 'QReg[T]) (F : finType) (phi : 'ONB(F;'Ht T))
  (c d : F -> ucmd_) {H : `{{forall i, ucmd_var_disj q (d i)}}}:
  <{[ (qif phi[q] = i then c i fiq) ; (qif phi[q] = i then d i fiq) ]}> =u 
    <{[ qif phi[q] = i then (sequ_ (c i) (d i)) fiq ]}>.
Proof.
rewrite eq_usem.unlock !usemE linear_suml/=.
apply eq_bigr=>i _; rewrite linear_sumr/= (bigD1 i)//= big1=>[j /negPf nji|];
rewrite !comp_lfunA -[X in X \o _ \o _]comp_lfunA 
  -liftf_lf_comp tf2f_comp outp_comp onb_dot ?eqxx.
by rewrite eq_sym nji scale0r tf2f0 linear0 comp_lfun0r !comp_lfun0l.
rewrite scale1r addr0 usemE comp_lfunA; do 2 f_equal.
move: (usem_local (d i))=>[U ->].
rewrite -comp_lfunA [in LHS]liftf_lf_compC.
by rewrite disjoint_sym; apply/ucmd_var_disj_vsetP.
by rewrite comp_lfunA -liftf_lf_comp tf2f_comp outp_comp onb_dot eqxx scale1r.
Qed.

Lemma qif_sequB (q : qreg Bool) phi c0 c1 d0 d1
  {H0 : `{{ucmd_var_disj q d0}}} {H1 : `{{ucmd_var_disj q d1}}} :
  <{[ (c0 ← phi[q] → c1) ; (d0 ← phi[q] → d1) ]}> =u 
    <{[ (c0 ; d0) ← phi[q] → (c1 ; d1) ]}>.
Proof.
have H : `{{forall i, ucmd_var_disj q (if i then d1 else d0)}} by case.
by rewrite qcond2_.unlock qif_sequG; apply: eq_qcondr; case.
Qed.

Lemma qif_sequ (q : qreg Bool) c0 c1 d0 d1
  {H0 : `{{ucmd_var_disj q d0}}} {H1 : `{{ucmd_var_disj q d1}}} :
  <{[ (c0 ← [q] → c1) ; (d0 ← [q] → d1) ]}> =u 
    <{[ (c0 ; d0) ← [q] → (c1 ; d1) ]}>.
Proof. exact: qif_sequB. Qed.

(* proposition 4.2 (8) : sequential composition, distributivity over qif *)
Lemma sequ_distrrG T (q : qreg T) (F : finType) (M : 'ONB(F;'Ht T)) c f
  {H : `{{ucmd_var_disj q c}}} :
  <{[ c ; (qif M[q] = i then f i fiq) ]}> =u 
    <{[ qif M[q] = i then sequ_ c (f i) fiq ]}>.
Proof.
rewrite eq_usem.unlock !usemE linear_suml/=.
apply eq_bigr=>i _; rewrite usemE -!comp_lfunA; do 2 f_equal.
move: (usem_local c)=>[U ->].
by rewrite liftf_lf_compC// disjoint_sym ucmd_var_disj_vsetP.
Qed.

Lemma sequ_distrlG T (q : qreg T) (F : finType) (M : 'ONB(F;'Ht T)) c f
  {H : `{{ucmd_var_disj q c}}} :
  <{[ (qif M[q] = i then f i fiq) ; c ]}> =u 
    <{[ qif M[q] = i then sequ_ (f i) c fiq ]}>.
Proof.
rewrite eq_usem.unlock !usemE linear_sumr/=.
apply eq_bigr=>i _; rewrite usemE !comp_lfunA; do 2 f_equal.
move: (usem_local c)=>[U ->].
by rewrite liftf_lf_compC// ucmd_var_disj_vsetP.
Qed.

Lemma sequ_distrrB q phi c c0 c1 {H : `{{ucmd_var_disj q c}}} :
  <{[ c ; (c0 ← phi[q] → c1) ]}> =u <{[ (c ; c0) ← phi[q] → (c ; c1) ]}>.
Proof.
by rewrite qcond2_.unlock sequ_distrrG; apply: eq_qcondr; case.
Qed.

Lemma sequ_distrlB q phi c c0 c1 {H : `{{ucmd_var_disj q c}}} :
  <{[ (c0 ← phi[q] → c1) ; c ]}> =u <{[ (c0 ; c) ← phi[q] → (c1 ; c) ]}>.
Proof. by rewrite qcond2_.unlock sequ_distrlG; apply: eq_qcondr; case. Qed.

Lemma sequ_distrr q c c0 c1 {H : `{{ucmd_var_disj q c}}} :
  <{[ c ; (c0 ← [q] → c1) ]}> =u <{[ (c ; c0) ← [q] → (c ; c1) ]}>.
Proof. exact: sequ_distrrB. Qed.

Lemma sequ_distrl q c c0 c1 {H : `{{ucmd_var_disj q c}}} :
  <{[ (c0 ← [q] → c1) ; c ]}> =u <{[ (c0 ; c) ← [q] → (c1 ; c) ]}>.
Proof. exact: sequ_distrlB. Qed.

Lemma liftf_lf_sum_comp (I : eqType) (r : seq I) (P : pred I) (S : {set mlab})
  (fT : I -> {set mlab}) (f : I -> 'F[msys]_S) (g : forall i, 'F_(fT i)) :
  (forall i, [disjoint S & fT i]%B) ->
  (forall i j, i != j -> f i \o f j = 0) ->
  (forall i, f i \o f i = f i) ->
  uniq r ->
  (\1 - (liftf_lf (\sum_(i <- r | P i) f i)) + \sum_(i <- r | P i) (liftf_lf (f i) \o (liftf_lf (g i)) \o (liftf_lf (f i))) = 
  \big[ (fun i j => comp_lfun j i) / \1 ]_(i <- r | P i) 
  (liftf_lf (\1 - f i) + (liftf_lf (f i) \o (liftf_lf (g i)) \o (liftf_lf (f i)))))%R.
Proof.
move=>P1 P2 P3.
elim: r=>[|a l IH].
by rewrite !big_nil linear0 addr0 subr0.
rewrite cons_uniq=>/andP[] Pa /IH IH1.
rewrite !big_cons; case: (P a)=>//.
rewrite -{}IH1 linearB linearD/= liftf_lf1.
set x1 := liftf_lf (\sum_(j <- l | _) _).
set x2 := \sum_(j <- l | _) _.
set x3 := liftf_lf (f a).
have P4: x1 \o x3 = 0.
by rewrite /x1 /x3 -liftf_lf_comp linear_suml/= big_seq_cond big1 ?linear0// 
  =>i /andP[] Pi _; move: (notin_in_neq Pa Pi); rewrite eq_sym; apply: P2.
have P5: x2 \o x3 = 0.
  rewrite /x2 /x3 linear_suml/= big_seq_cond big1// =>i /andP[] Pi _.
  move: (notin_in_neq Pa Pi); rewrite eq_sym -!comp_lfunA -liftf_lf_comp=>/P2->;
  by rewrite linear0 !comp_lfun0r.
rewrite linearDr/= linearBr/= comp_lfun1r linearDl/= linearBl/= 
  P4 P5 subr0 addr0 linearDl/= linearBl/= !comp_lfun1l !comp_lfunA P4 P5
  !comp_lfun0l subr0 addr0 addrA addrC !addrA; f_equal.
by rewrite opprD addrACA addrC addrA.
Qed.

(* equation (13) , splitting *)
Lemma qcond_split T (x : 'QReg[T]) (phi : 'ONB) (f : evalQT T -> ucmd_) 
  {H0 : forall i, (ucmd_var_disj x (f i))} :
  <{[ qif phi[x] = i then f i fiq ]}> =u 
    \big[sequ_/uskip_]_i <{[ phi[x] →_(i) (f i) ]}>.
Proof.
rewrite eq_usem.unlock usemE usem_big.
pose fi i := tf2f x x [> phi i; phi i <].
pose gi i := projT1 (cid (usem_local (f i))).
have Pi i : usem (qcond_ x phi (fun j : evalQT T => if j == i then f i else uskip_))
  = ((liftf_lf (\1 - fi i) + (liftf_lf (fi i) \o (liftf_lf (gi i)) \o (liftf_lf (fi i)))))%R.
  rewrite usemE (bigD1 i)//= eqxx addrC; f_equal;
    last by rewrite (projT2 (cid (usem_local (f i)))).
  have <-: \sum_i (fi i) = \1 by rewrite /fi -linear_sum/= sumonb_out tf2f1.
  rewrite [in RHS](bigD1 i)//= addrC addKr linear_sum/=.
  by apply eq_bigr=>j /negPf ->; rewrite usemE comp_lfun1r 
    -liftf_lf_comp tf2f_comp outp_comp ns_dot scale1r.
under [RHS]eq_bigr do rewrite Pi.
rewrite -liftf_lf_sum_comp ?index_enum_uniq// =>[i|i j /negPf nij | i |].
by apply/ucmd_var_disj_vsetP.
by rewrite /fi tf2f_comp outp_comp onb_dot nij scale0r tf2f0.
by rewrite /fi tf2f_comp outp_comp ns_dot scale1r.
rewrite /fi -linear_sum/= sumonb_out tf2f1 liftf_lf1 addrN add0r.
by apply eq_bigr=>i _; do 2 f_equal; move: (projT2 (cid (usem_local (f i)))).
Qed.

(* proposition 4.3 (1) : quantum choice, symmetry *)
Lemma qchoice_sym (q : qreg Bool) c0 c1 
  {H0 : `{{ucmd_var_disj q c0}}} {H1 : `{{ucmd_var_disj q c1}}} :
  <{[ c0 ← {''X}[q] → c1 ]}> =u <{[ c1 ← [q]{''X} → c0 ]}>.
Proof.
rewrite eq_usem.unlock !usemE addrC comp_lfunDl comp_lfunDr; f_equal.
move: (usem_local c0)=>[U ->]. 2: move: (usem_local c1)=>[U ->].
all: rewrite !comp_lfunA -liftf_lf_comp ![_ \o liftf_lf U]liftf_lf_compC 
  ?ucmd_var_disj_vsetP// -!comp_lfunA; f_equal; 
  by rewrite -!liftf_lf_comp !tf2f_comp !outp_compr !outp_compl 
    PauliX_adj !PauliX_cb/= adj_outp !outpE !onb_dot !eqxx !scale1r.
Qed.

Lemma qchoice_symG (q : qreg Bool) (phi : 'ONB) (psi : 'ONB) c0 c1 
  {H0 : `{{ucmd_var_disj q c0}}} {H1 : `{{ucmd_var_disj q c1}}} :
  <{[ c0 ← {(onb_change phi psi)}psi[q] → c1 ]}> =u 
    <{[ c0 ← phi[q]{(onb_change phi psi)} → c1 ]}>.
Proof.
rewrite eq_usem.unlock !usemE !linearDl/= !linearDr/=; f_equal.
move: (usem_local c1)=>[U ->]. 2: move: (usem_local c0)=>[U ->].
all: rewrite !comp_lfunA -liftf_lf_comp ![_ \o liftf_lf U]liftf_lf_compC 
  ?ucmd_var_disj_vsetP// -!comp_lfunA; f_equal.
all: by rewrite -!liftf_lf_comp !tf2f_comp !outp_compr !outp_compl
  onb_change_adj !onb_changeE adj_outp !outpE !onb_dot eqxx !scale1r.
Qed.

Lemma qchoice_symGP (q : qreg Bool) (phi : 'ONB) (psi : 'ONB) c0 c1 (U : 'FU)
  {H0 : `{{ucmd_var_disj q c0}}} {H1 : `{{ucmd_var_disj q c1}}} :
  U = onb_change phi psi :> 'End(_) ->
  <{[ c0 ← {U}psi[q] → c1 ]}> =u <{[ c0 ← phi[q]{U} → c1 ]}>.
Proof. by move=>/eq_unitary->; exact: qchoice_symG. Qed.

(* proposition 4.3 (2) : quantum choice, sequentiality *)
Lemma qchoicel_sequG (q : qreg Bool) b phi c0 c1 d0 d1
  {H0 : `{{ucmd_var_disj q d0}}} {H1 : `{{ucmd_var_disj q d1}}} :
  <{[ b ; (c0 ← phi [q] → c1) ; (d0 ← phi[q] → d1) ]}> =u 
    <{[ b ; (c0 ; d0) ← phi[q] → (c1 ; d1) ]}>.
Proof. by rewrite sequA qif_sequB. Qed.

Lemma qchoicel_sequ (q : qreg Bool) b c0 c1 d0 d1
  {H0 : `{{ucmd_var_disj q d0}}} {H1 : `{{ucmd_var_disj q d1}}} :
  <{[ (c0 ← {{b}}[q] → c1) ; (d0 ← [q] → d1) ]}> =u 
    <{[ (c0 ; d0) ← {{b}}[q] → (c1 ; d1) ]}>.
Proof. exact: qchoicel_sequG. Qed.

Lemma qchoicer_sequG (q : qreg Bool) b phi c0 c1 d0 d1
  {H0 : `{{ucmd_var_disj q d0}}} {H1 : `{{ucmd_var_disj q d1}}} :
  <{[ (c0 ← phi[q] → c1) ; ((d0 ← phi[q] → d1) ; b) ]}> =u 
    <{[ (c0 ; d0) ← phi[q] → (c1 ; d1) ; b ]}>.
Proof. by rewrite -sequA qif_sequB. Qed.

Lemma qchoicer_sequ (q : qreg Bool) b c0 c1 d0 d1
  {H0 : `{{ucmd_var_disj q d0}}} {H1 : `{{ucmd_var_disj q d1}}} :
  <{[ (c0 ← [q] → c1) ; (d0 ← [q]{{b}} → d1) ]}> =u 
    <{[ (c0 ; d0) ← [q]{{b}} → (c1 ; d1) ]}>.
Proof. exact: qchoicer_sequG. Qed.

(* proposition 4.3 (3) : quantum choice, distributivity *)
Lemma qchoicel_distrrB (q : qreg Bool) phi c d c0 c1
  {H1 : `{{ucmd_var_disj q c}}} {H2 : `{{ucmd_var_subset q d}}} :
  <{[ c ; (d ; (c0 ← phi[q] → c1)) ]}> =u 
    <{[ d ; (c ; c0) ← phi[q] → (c ; c1) ]}>.
Proof.
rewrite -sequA (@sequC c d _).
  rewrite ucmd_disjE fdisjoint_sym; move: H2 H1; 
  by rewrite ucmd_var_disjE; apply: fdisjointWl.
by rewrite sequA (@sequ_distrrB q phi c c0 c1 _).
Qed.

Lemma qchoicel_distrlB (q : qreg Bool) phi c d c0 c1 {H : `{{ucmd_var_disj q c}}} :
  <{[ d ; (c0 ← phi[q] → c1) ; c ]}> =u <{[ d ; (c0 ; c) ← phi[q] → (c1 ; c) ]}>.
Proof. by rewrite sequA sequ_distrlB. Qed.

Lemma qchoicer_distrrB (q : qreg Bool) phi c d c0 c1 {H : `{{ucmd_var_disj q c}}} :
  <{[ c ; ((c0 ← phi[q] → c1) ; d) ]}> =u <{[ (c ; c0) ← phi[q] → (c ; c1) ; d ]}>.
Proof. by rewrite -sequA sequ_distrrB. Qed.

Lemma qchoicer_distrlB (q : qreg Bool) phi c d c0 c1
  {H1 : `{{ucmd_var_disj q c}}} {H2 : `{{ucmd_var_subset q d}}} :
  <{[ (c0 ← phi[q] → c1) ; d ; c ]}> =u <{[ (c0 ; c) ← phi[q] → (c1 ; c) ; d ]}>.
Proof.
rewrite sequA -(@sequC c d _).
  rewrite ucmd_disjE fdisjoint_sym; move: H2 H1; 
  by rewrite ucmd_var_disjE; apply: fdisjointWl.
by rewrite -sequA sequ_distrlB.
Qed.

Lemma qchoicel_distrr (q : qreg Bool) c d c0 c1
  {H1 : `{{ucmd_var_disj q c}}} {H2 : `{{ucmd_var_subset q d}}} :
  <{[ c ; (d ; (c0 ← [q] → c1)) ]}> =u 
    <{[ d ; (c ; c0) ← [q] → (c ; c1) ]}>.
Proof. exact: qchoicel_distrrB. Qed.

Lemma qchoicel_distrl (q : qreg Bool) c d c0 c1 {H : `{{ucmd_var_disj q c}}} :
  <{[ d ; (c0 ← [q] → c1) ; c ]}> =u <{[ d ; (c0 ; c) ← [q] → (c1 ; c) ]}>.
Proof. exact: qchoicel_distrlB. Qed.

Lemma qchoicer_distrr (q : qreg Bool)  c d c0 c1 {H : `{{ucmd_var_disj q c}}} :
  <{[ c ; ((c0 ← [q] → c1) ; d) ]}> =u <{[ (c ; c0) ← [q] → (c ; c1) ; d ]}>.
Proof. exact: qchoicer_distrrB. Qed.

Lemma qchoicer_distrl (q : qreg Bool)  c d c0 c1
  {H1 : `{{ucmd_var_disj q c}}} {H2 : `{{ucmd_var_subset q d}}} :
  <{[ (c0 ← [q] → c1) ; d ; c ]}> =u <{[ (c0 ; c) ← [q] → (c1 ; c) ; d ]}>.
Proof. exact: qchoicer_distrlB. Qed.

End CircuitLaws.

(*****************************************************************************)
(*               Normal form of quantum circuits (Section 4.2)               *)
(* Given a regular circuit, we give the syntactically construction of the    *)
(* normal circuits that are semantically equivalent                          *)
(*****************************************************************************)
Section CircuitNormalForm.
(* Assumption : BU is the basic-gate sets *)
Variable (BU : forall T : qType, 'End{T} -> bool).

(*------------------------------------------------------*)
(*                Definition 4.2 (1)(b)                 *)
(* A basic circuit is a sequential composition of basic *)
(* quantum gates or uskip                               *)
(*------------------------------------------------------*)
Inductive basic_circuit : ucmd_ -> Type :=
  (* skip is basic *)
  | basic_uskip : basic_circuit uskip_
  (* unitary is a basic gate *)
  | basic_unitary (T : qType) (x : qreg T) (U : 'FU('Ht T)) (bu : BU U) : 
      basic_circuit <{[ [x] *= U ]}>
  (* sequential of basic circuits *)
  | basic_sequ u1 u2 (H1 : basic_circuit u1) (H2 : basic_circuit u2) : 
      basic_circuit <{[ u1; u2 ]}>.

(*------------------------------------------------------*)
(*                 weak normal circuit                  *)
(* A weak normal circuit is a sequential composition of *)
(* flat quantum if-statement or basic_circuit           *)
(*------------------------------------------------------*)
Inductive wnormal_circuit : ucmd_ -> Type :=
  (* basic circuit is weak normal *)
  | wnormal_basic u (H : basic_circuit u) : wnormal_circuit u
  (* qif is flat, i.e., the guard is in computational basis, *)
  (* each branch is a basic circuit                          *)
  | wnormal_qcond (T : qType) (x : qreg T) (f : (evalQT T) -> ucmd_) 
    (H : forall i, basic_circuit (f i)) :
      wnormal_circuit <{[qif [x] = i then f i fiq]}>
  (* sequential of weak normal circuits *)
  | wnormal_sequ u1 u2 (H1 : wnormal_circuit u1) (H2 : wnormal_circuit u2) :
      wnormal_circuit <{[ u1; u2 ]}>.

Lemma wnormal_qcond2 (x : qreg Bool) c0 c1 :
  basic_circuit c0 -> basic_circuit c1 ->
    wnormal_circuit <{[ c0 ← [x] → c1 ]}>.
Proof. by move=>P0 P1; rewrite qcond2_.unlock; apply: wnormal_qcond=>[[]]. Qed.

(*------------------------------------------------------*)
(*                  Definition 4.2 (2)                  *)
(* A normal circuit is a sequential composition of flat *)
(* quantum if-statement                                 *)
(*------------------------------------------------------*)
Inductive normal_circuit : ucmd_ -> Type :=
  (* qif is flat, i.e., the guard is in computational basis, *)
  (* each branch is a basic circuit                          *)
  | normal_qcond (T : qType) (x : qreg T) (f : (evalQT T) -> ucmd_) 
    (H : forall i, basic_circuit (f i)) :
      normal_circuit <{[qif [x] = i then f i fiq]}>
  (* sequential of normal circuits *)
  | normal_sequ u1 u2 (H1 : normal_circuit u1) (H2 : normal_circuit u2) :
      normal_circuit <{[ u1; u2 ]}>.

(* wrapped normal circuit, i.e., circuit with a proof that it is normal *)
Record wrap_normal_circuit := Normal_Circuit 
  {ucmd_normal : ucmd_ ; is_normal_circuit : normal_circuit ucmd_normal}.
Coercion ucmd_normal : wrap_normal_circuit >-> ucmd_.

(* wrapped basic circuit, i.e., circuit with a proof that it is basic *)
Record wrap_basic_circuit := Basic_Circuit 
  {ucmd_basic : ucmd_ ; is_basic_circuit : basic_circuit ucmd_basic}.
Coercion ucmd_basic : wrap_basic_circuit >-> ucmd_.

(* wrapped weak normal circuit, i.e., circuit with a proof that it is weak normal *)
Record wrap_wnormal_circuit := WNormal_Circuit 
  {ucmd_wnormal : ucmd_ ; is_wnormal_circuit : wnormal_circuit ucmd_wnormal}.
Coercion ucmd_wnormal : wrap_wnormal_circuit >-> ucmd_.

Lemma normal_qcond2 (x : qreg Bool) c0 c1 :
  basic_circuit c0 -> basic_circuit c1 ->
    normal_circuit <{[ c0 ← [x] → c1 ]}>.
Proof. by move=>P0 P1; rewrite qcond2_.unlock; apply: normal_qcond=>[[]]. Qed.

Lemma normal_weak u : normal_circuit u -> wnormal_circuit u.
Proof.
elim; first by move=>????; apply: wnormal_qcond.
by move=> u1 u2 ? P1 ? P2; apply: wnormal_sequ.
Qed.

Local Open Scope fset_scope.

(*------------------------------------------------------*)
(*                    Definition 4.3                    *)
(* An orthonormal basis {|phi_i>} is called basic, if   *)
(* there exists basic circuits that transform {|phi_i>} *)
(* to computational basis {|i>} and transform {|i>} to  *)
(* {|phi_i>} ; we require the circuits are well-formed  *)
(* and only acting on the same/smaller quantum register *)
(*------------------------------------------------------*)
Definition basic_onb (T : qType) (phi : 'ONB(evalQT T; 'Ht T)) (x : qreg T) : Type :=
  { u : wrap_basic_circuit | (ucmd_var_basic u `<=` x) /\ ucmd_wf u &
    (usem u = liftf_lf (tf2f x x (onb_change phi t2tv)))} *
  { u : wrap_basic_circuit | (ucmd_var_basic u `<=` x) /\ ucmd_wf u &
    (usem u = liftf_lf (tf2f x x (onb_change t2tv phi)))}.

(*------------------------------------------------------*)
(*                    Definition 4.3                    *)
(* A circuit is regular, if it is a composition of :    *)
(* uskip, basic gates, quantum if with basic onb as     *)
(* guard and regular circuits as branches               *)
(*------------------------------------------------------*)
Inductive regular_circuit : ucmd_ -> Type :=
  | Regular_uskip : regular_circuit uskip_
  | Regular_unitary (T : qType) (x : qreg T) (U : 'FU('Ht T)) (bu : BU U) : 
      regular_circuit <{[ [x] *= U ]}>
  | Regular_qcond (T : qType) (x : qreg T) (phi : 'ONB) (f : (evalQT T) -> ucmd_) 
      (HM : basic_onb phi x) (Hc : forall i, regular_circuit (f i)) :
      regular_circuit <{[ qif phi[x] = i then f i fiq ]}>
  | Regular_sequ u1 u2 (H1 : regular_circuit u1) (H2 : regular_circuit u2) : 
      regular_circuit <{[ u1; u2 ]}>.

(* Here, we give the construction from regular circuit to normal circuit *)
Fixpoint qcond_map T (x : qreg T) (i : evalQT T) (f : ucmd_) :=
  match f with
  | uskip_ => qcond_ x t2tv (fun => uskip_)
  | unitary_ _ x1 u => qcond_ x t2tv (fun j : evalQT T => if j == i then unitary_ x1 u else uskip_)
  | qcond_ T1 F1 x1 phi f1 =>
      qcond_ <{(x,x1)}> (tentv_onbasis t2tv phi) (fun j : evalQT T * F1 => 
      if (j.1 == i) then (f1 j.2) else uskip_)
  | sequ_ u1 u2 => sequ_ (qcond_map x i u1) (qcond_map x i u2)
  end.

Fixpoint regular_to_wnormal (u : ucmd_) (H : regular_circuit u) : ucmd_ :=
  match H with
  | Regular_uskip => uskip_
  | Regular_unitary T x U bu => unitary_ x U
  | Regular_qcond T x phi f HM Hc => 
      sequ_ (sequ_ (projT1 HM.1) 
            (\big[sequ_ / uskip_]_i qcond_map x i (regular_to_wnormal (Hc i)))) 
            (projT1 HM.2)
  | Regular_sequ u1 u2 H1 H2 =>
      sequ_ (regular_to_wnormal H1) (regular_to_wnormal H2)
  end.

Fixpoint wnormal_to_normal T (x : qreg T) (u : ucmd_) (H : wnormal_circuit u) : ucmd_ :=
  match H with
  | wnormal_basic u _ => qcond_ x t2tv (fun i => u)
  | wnormal_qcond T1 x1 f _ => qcond_ x1 t2tv f
  | wnormal_sequ u1 u2 H1 H2 => 
      sequ_ (wnormal_to_normal x H1) (wnormal_to_normal x H2)
  end.

(* the construction regular_to_wnormal indeed gives a weak normal circuit *)
Lemma regular_to_wnormal_wnormal (u : ucmd_) (H : regular_circuit u) :
  wnormal_circuit (regular_to_wnormal H).
Proof.
elim: H=>/=.
- by apply/wnormal_basic/basic_uskip.
- by move=>T x U bu; apply/wnormal_basic/basic_unitary.
- move=>T x phi f HM Hc Pi.
  apply/wnormal_sequ; last by apply/wnormal_basic/is_basic_circuit.
  apply/wnormal_sequ; first by apply/wnormal_basic/is_basic_circuit.
  elim: (index_enum _)=>[|i l IH].
  - by rewrite big_nil; apply/wnormal_basic/basic_uskip.
  - rewrite big_cons; apply/wnormal_sequ=>//.
    move: (Pi i); elim=>/=.
    - move=>u1; elim=>/=.
      - by apply/wnormal_qcond=> _; apply/basic_uskip.
      - move=>T1 x1 U bu; apply/wnormal_qcond=>j; case: eqP=> _;
        by [apply/basic_unitary | apply/basic_uskip].
      - by move=>??????; apply/wnormal_sequ.
    - move=>T1 x1 f1 Hi.
      have ->: (tentv_onbasis t2tv t2tv) = t2tv :> 'ONB.
        by move=>??; apply/eq_onb=>[[i1 i2]]; rewrite/= /tentv_fun/= tentv_t2tv.
      by apply/wnormal_qcond=>j; case: eqP=>// _; apply/basic_uskip.
    - by move=>??????; apply/wnormal_sequ.
- by move=>??????; apply/wnormal_sequ.
Qed.

(*---------------------------------------------------------------------------*)
(* if u is a well-formed regular circuit, then regular_to_wnormal u :        *)
(*   1. doesn't increase the variable set, i.e., we don't need auxiliary     *)
(*      variables                                                            *)
(*   2. it is well-formed;                                                   *)
(*   3. it is equivelant to u (semantically)                                 *)
(*---------------------------------------------------------------------------*)
Lemma regular_to_wnormalP u (H : regular_circuit u) : ucmd_wf u ->
  let uw := regular_to_wnormal H in
  (ucmd_var_basic uw `<=` ucmd_var_basic u)%fset /\ ucmd_wf uw /\ u =u uw.
Proof.
rewrite/=; elim: H; clear u=>//=; last first.
  (* construction of seq *)
  move=>u1 u2 H1 IH1 H2 IH2 /andP[] Pu1 Pu2.
  move: (IH1 Pu1) (IH2 Pu2)=>[] + [] -> {3}-> [] + [] -> {3}->; do ! split=>//.
  by apply: fsetUSS.
(* construction of qif *)
move=>T x phi f HM Hc IH /andP[] Px /forallP Pi; do ! split.
(* disjointness of variables *)
- apply/fsubUsetP; split; last by apply/fsubsetU/orP; left; move: (projT2 HM.2)=>[][].
  apply/fsubUsetP; split; first by apply/fsubsetU/orP; left; move: (projT2 HM.1)=>[][].
  rewrite ucmd_var_basic_big; apply/bigfcupsP=>i _ _.
  rewrite (bigD1 i)//= fsetUA; apply/fsubsetU/orP; left.
  move: (Pi i)=>/andP[]/IH[] + _ _.
  elim: (regular_to_wnormal_wnormal (Hc i))=>/=.
    - move=>u; elim=>/=.
      - by move=>_; apply/fsetUS/bigfcupsP.
      - by move=>?????; apply/fsetUS/bigfcupsP=>? _ _; case: eqP.
      - by move=>??? IH1? IH2 /fsubUsetP[]/IH1 ? /IH2 ?; apply/fsubUsetPP.
    - move=>T1 x1 f1 _ P; rewrite fset_qreg_pair -fsetUA; apply/fsetUS.
      rewrite pair_bigV/= (bigD1 i)//= fsetUA [X in _ `|` _ `|` X]big1.
        by move=>j /negPf nji; rewrite big1// =>? _; rewrite nji.
      by under eq_bigr do rewrite eqxx; rewrite fsetU0.
    - by move=>u1 u2 H1 IH1 H2 IH2 /fsubUsetP[] /IH1 P1 /IH2 P2; apply/fsubUsetP.
(* well-formedness *)
- apply/andP; split; last by move: (projT2 HM.2)=>[][].
  apply/andP; split; first by move: (projT2 HM.1)=>[][].
  elim: (index_enum _)=>[|i l IH1]; first by rewrite big_nil.
  rewrite big_cons/= IH1 andbT.
  move: (Pi i)=>/andP[] /IH [] + [] + _.
  elim: (regular_to_wnormal_wnormal (Hc i))=>/=.
    - move=>u; elim=>/=.
      - by move=>_ _ _; rewrite Px/=; apply/forallP.
      - move=>T1 x1 U bu P1 Pu Pdis; rewrite Px/=; apply/forallP=>j.
        apply/andP; split; case: eqP=>//= _; rewrite fdisjoint_qregP.
        by move: Pdis; rewrite !ucmd_var_disjE; apply/fdisjointWr.
      - by move=>??? H1? H2 /fsubUsetP[]/H1 H3 /H2 H4/andP[] /H3 H5 /H4 H6 ?; rewrite H5// H6.
    - move=>T1 x1 f1 _ P1 /andP [] Px1 /forallP Pdx Pdis; apply/andP.
      have dis: disjoint_qreg x x1.
        move: P1 Pdis=>/fsubUsetP[] P2 _; rewrite ucmd_var_disjE=>P3.
        by move: (fdisjointWr P2 P3); rewrite fdisjoint_qregP.
      split. QRegAuto.tac_expose.
      apply/forallP=>j; apply/andP; split; case: eqP=>// _.
        by move: (Pdx j.2)=>/andP[].
        rewrite ucmd_var_disjE fset_qreg_pair fdisjointUX; apply/andP; split.
          by move: P1=>/fsubUsetP[] _ /bigfcupsP/(_ j.2 (@mem_index_enum _ _))
            /(_ is_true_true)/fdisjointWr; apply; rewrite -ucmd_var_disjE.
        by move: (Pdx j.2)=>/andP[] _; rewrite ucmd_var_disjE.
    - move=>u1 u2 H1 P1 H2 P2 /fsubUsetP[] Pu1 Pu2 /andP[] Pw1 Pw2 dis.
      by apply/andP; split; [apply/P1|apply/P2].
(* semantics *)
have H0 : `{{ forall i, ucmd_var_disj x (f i)}}.
  by move=>i; move: (Pi i)=>/andP[].
rewrite qif_change_basisG/= eq_usem.unlock usemE [RHS]usemE; f_equal.
  by move: (projT2 HM.2)=>[] _ ->; rewrite usemE.
rewrite usemE [RHS]usemE; f_equal; last first.
  by move: (projT2 HM.1)=>[] _ ->; rewrite usemE.
apply/eq_usemE; rewrite qcond_split/=.
  by move=>i; move: (Pi i)=>/andP[].
apply/eq_bigr_usem=>i _; move: (Pi i)=>/andP[]/IH[] P1 [] P2 Pf Pdis.
apply: (eq_usem_trans (b := <{[ qif [x] = j then 
  if j == i then (regular_to_wnormal (Hc i) : ucmd_) else <{[ uskip ]}> fiq ]}>)).
  by apply eq_qcondr=>j; rewrite /if_fun; case: eqP.
move: P1 P2.
elim: (regular_to_wnormal_wnormal (Hc i))=>/=.
  - move=>u; elim=>//=.
    - by move=>_ _; apply/eq_qcondr=>j; case: eqP.
    - move=>? u2? H1? H2 /fsubUsetP[]/H1 H3 Hu.
      move: {+}Hu => /H2 H4/andP[] /H3 <- /H4 <-.
      have P : `{{forall j, ucmd_var_disj x (if j == i then u2 else <{[ uskip ]}>)}}.
        move=>j; case: eqP=>//= _; move: Pdis.
        by rewrite !ucmd_var_disjE; apply/fdisjointWr.
      rewrite qif_sequG/=; apply eq_qcondr=>j; case: eqP=>// _; 
      by rewrite eq_usem.unlock !usemE comp_lfun1r.
  - move=>T1 x1 f1 _ P1 /andP[] Px1 /forallP Pi1.
    have dis: `{{disjoint_qreg x x1}}.
      move: P1 Pdis=>/fsubUsetP[] P2 _; rewrite ucmd_var_disjE=>P3.
      by move: (fdisjointWr P2 P3); rewrite fdisjoint_qregP.
    rewrite -(qif_nestlGB _ _(fun j1 j2 => if j1 == i then f1 j2 else <{[ uskip ]}>))/=.
    apply/eq_qcondr=>j1; case: eqP=>// _.
    rewrite eq_usem.unlock !usemE.
    under eq_bigr do rewrite comp_lfun1r -liftf_lf_comp tf2f_comp outp_comp ns_dot scale1r.
    by rewrite -!linear_sum/= sumonb_out tf2f1 liftf_lf1.
  - move=>u1 u2 H1 IH1 H2 IH2 /fsubUsetP[] P1 P2 /andP[] P3 P4.
    rewrite -(IH1 P1 P3) -(IH2 P2 P4).
    have Pd: forall j, ucmd_var_disj x ((fun j : evalQT T =>if j == i then u2 else <{[ uskip ]}>) j).
      by move=>j; case: eqP=>// _; move: Pdis; rewrite !ucmd_var_disjE; apply/fdisjointWr.
    rewrite (@qif_sequG _ _ _ _ _ _ Pd)/=; apply eq_qcondr=>j.
    by case: eqP=>// _; rewrite eq_usem.unlock !usemE comp_lfun1r.
Qed.

(* the construction wnormal_to_normal indeed gives a normal circuit *)
Lemma wnormal_to_normal_normal T (x : qreg T) (u : ucmd_) (H : wnormal_circuit u) :
  normal_circuit (wnormal_to_normal x H).
Proof.
elim: H=>//=; clear.
by move=>u bu; apply/normal_qcond.
by move=>T x f IH; apply/normal_qcond.
by move=>??????; apply/normal_sequ.
Qed.

(*****************************************************************************)
(*                          Theorem 4.1 (Normal Form)                        *)
(*---------------------------------------------------------------------------*)
(* given a well-formed regular circuit u and a disjoint quantum variable x,  *)
(* let uw := wnormal_to_normal x (regular_to_wnormal_wnormal ru)), we claim: *)
(*   1. uw is syntactically constructed from u, as it is defined;            *)
(*   2. uw is well-formed;                                                   *)
(*   3. u =u uw, i.e., uw is equivalent to u (semantically)                  *)
(*****************************************************************************)
Lemma regular_normal (x : qreg Bool) u (ru : regular_circuit u) :
  ucmd_wf u -> ucmd_var_disj x u ->
  let uw := wnormal_to_normal x (regular_to_wnormal_wnormal ru) in
    ucmd_wf uw /\ u =u uw.
Proof.
move=>/= Pu Px; split.
  move: (regular_to_wnormalP ru Pu)=>/=[] + [] + _.
  elim: (regular_to_wnormal_wnormal ru)=>//.
  - move=>u1 H1 /= P1 P2; apply/andP; split; first by QRegAuto.tac_expose.
    by apply/forallP=> _; rewrite P2/=; move: Px; rewrite !ucmd_var_disjE; apply/fdisjointWr.
  - by move=>u1 u2 H1 IH1 H2 IH2 /= /fsubUsetP[] /IH1 H3 /IH2 H4 /andP[] /H3 -> /H4 ->.
move: (regular_to_wnormalP ru Pu)=>/=[] + [] _ {1}->.
elim: (regular_to_wnormal_wnormal ru)=>//.
  move=>u1 H1 P1 /=.
  have P : `{{ucmd_var_disj x u1}}.
    by move: Px; rewrite !ucmd_var_disjE; apply/fdisjointWr.
  by rewrite qif_idemG.
by move=>u1 u2 H1 IH1 H2 IH2 /= /fsubUsetP[]/IH1 {1}->/IH2 {1}->.
Qed.

End CircuitNormalForm.

(*****************************************************************************)
(*                                 Automation                                *)
(*****************************************************************************)

(* solving cmd_expose *)
(*
forall i, (ucmd_var_disj q (c i))
ucmd_var_disj q c0
disjoint_qreg q1 q2
ucmd_disj u1 u2
ucmd_var_subset q d
ucmd_wf *)
Module Export CircuitAuto.

HB.lock Definition ucmd_var_disj_lock := ucmd_var_disj.
Lemma ucmd_var_disj_lockE : ucmd_var_disj = ucmd_var_disj_lock.
Proof. by rewrite ucmd_var_disj_lock.unlock. Qed.
HB.lock Definition ucmd_disj_lock := ucmd_disj.
Lemma ucmd_disj_lockE : ucmd_disj = ucmd_disj_lock.
Proof. by rewrite ucmd_disj_lock.unlock. Qed.
HB.lock Definition ucmd_var_subset_lock := ucmd_var_subset.
Lemma ucmd_var_subset_lockE : ucmd_var_subset = ucmd_var_subset_lock.
Proof. by rewrite ucmd_var_subset_lock.unlock. Qed.
HB.lock Definition ucmd_wf_lock := ucmd_wf.
Lemma ucmd_wf_lockE : ucmd_wf = ucmd_wf_lock.
Proof. by rewrite ucmd_wf_lock.unlock. Qed.

Lemma ucmd_var_disj_lock_uskip T (x : qreg T) : ucmd_var_disj_lock x uskip_.
Proof. by rewrite -ucmd_var_disj_lockE. Qed.

Lemma ucmd_var_disj_lock_unitary T1 T2 (x1 : qreg T1) (x2 : qreg T2) U :
  disjoint_qreg x1 x2 -> ucmd_var_disj_lock x1 (unitary_ x2 U).
Proof. by rewrite -ucmd_var_disj_lockE. Qed.

Lemma ucmd_var_disj_lock_sequ T (x : qreg T) u1 u2 :
  ucmd_var_disj_lock x u1 -> ucmd_var_disj_lock x u2 -> ucmd_var_disj_lock x (sequ_ u1 u2).
Proof. by rewrite -!ucmd_var_disj_lockE/==>->->. Qed.

Lemma ucmd_var_disj_lock_qcond2 T (x : qreg T) (y : qreg Bool) phi u0 u1 :
  disjoint_qreg x y -> ucmd_var_disj_lock x u0 -> ucmd_var_disj_lock x u1 ->
  ucmd_var_disj_lock x (qcond2_ y phi u0 u1).
Proof.
by rewrite -!ucmd_var_disj_lockE qcond2_.unlock/= =>-> P2 P3/=; apply/forallP; case.
Qed.

Lemma ucmd_var_disj_lock_qcond T1 T2 (F : finType) 
  (x1 : qreg T1) (x2 : qreg T2) phi (f : F -> ucmd_):
  disjoint_qreg x1 x2 -> (forall i, ucmd_var_disj_lock x1 (f i)) ->
    ucmd_var_disj_lock x1 (qcond_ x2 phi f).
Proof. by rewrite -!ucmd_var_disj_lockE/==>->/=/forallP. Qed.

Lemma ucmd_var_disj_lock_if T (x : qreg T) b u0 u1 :
  ucmd_var_disj_lock x u0 -> ucmd_var_disj_lock x u1 ->
    ucmd_var_disj_lock x (if b then u0 else u1).
Proof. by case: b. Qed.

Ltac tac_ucmd_var_disj := repeat match goal with
  | [ |- forall _ , _ ] => intros; 
          rewrite /= ?(eq_qreg_fst, eq_qreg_snd, eq_qreg_tuplei, eq_qreg_ffuni)/=
  | [ H : is_true (ucmd_var_disj_lock ?x ?y) |- is_true (ucmd_var_disj_lock ?x ?y) ] => 
          apply H
  | [ |- is_true (ucmd_var_disj_lock _ uskip_)] => 
          apply/ucmd_var_disj_lock_uskip
  | [ |- is_true (ucmd_var_disj_lock _ (unitary_ _ _))] => 
          apply/ucmd_var_disj_lock_unitary
  | [ |- is_true (ucmd_var_disj_lock _ (sequ_ _ _))] => 
          apply/ucmd_var_disj_lock_sequ
  | [ |- is_true (ucmd_var_disj_lock _ (qcond2_ _ _ _ _))] => 
          apply/ucmd_var_disj_lock_qcond2
  | [ |- is_true (ucmd_var_disj_lock _ (qcond_ _ _ _))] => 
          apply/ucmd_var_disj_lock_qcond
  | [ |- is_true (ucmd_var_disj_lock _ (if _ then _ else _)) ] =>
          rewrite ?eqxx/=; try apply/ucmd_var_disj_lock_if
  | [ |- is_true (disjoint_qreg _ _) ] => QRegAuto.tac_expose
end.

Lemma ucmd_disj_lock_uskip u : ucmd_disj_lock uskip_ u.
Proof. by rewrite -ucmd_disj_lockE. Qed.

Lemma ucmd_disj_lock_unitary T (x : qreg T) U u :
  ucmd_var_disj_lock x u -> ucmd_disj_lock (unitary_ x U) u.
Proof. by rewrite -ucmd_disj_lockE/= ucmd_var_disj_lock.unlock. Qed.

Lemma ucmd_disj_lock_sequ u1 u2 u :
  ucmd_disj_lock u1 u -> ucmd_disj_lock u2 u -> ucmd_disj_lock (sequ_ u1 u2) u.
Proof. by rewrite -!ucmd_disj_lockE/==>->->. Qed.

Lemma ucmd_disj_lock_qcond2 (x : qreg Bool) phi u0 u1 u :
  ucmd_var_disj_lock x u -> ucmd_disj_lock u0 u -> ucmd_disj_lock u1 u ->
  ucmd_disj_lock (qcond2_ x phi u0 u1) u.
Proof.
rewrite -!ucmd_disj_lockE qcond2_.unlock/= ucmd_var_disj_lock.unlock;
by move=>-> P2 P3/=; apply/forallP; case.
Qed.

Lemma ucmd_disj_lock_qcond T (F : finType) (x : qreg T) phi (f : F -> ucmd_) u :
  ucmd_var_disj_lock x u -> (forall i, ucmd_disj_lock (f i) u) ->
  ucmd_disj_lock (qcond_ x phi f) u.
Proof. by rewrite -!ucmd_var_disj_lockE -!ucmd_disj_lockE/==>-> /forallP. Qed.

Lemma ucmd_disj_lock_if b u0 u1 u :
  ucmd_disj_lock u0 u -> ucmd_disj_lock u1 u ->
    ucmd_disj_lock (if b then u0 else u1) u.
Proof. by case: b. Qed.

Lemma ucmd_disjC u1 u2 : ucmd_disj u1 u2 = ucmd_disj u2 u1.
Proof.
elim: u1 u2=>/=.
- elim=>//=[?->?->|????? IH]; first by rewrite andbb.
  by symmetry; apply/forallP.
- move=>T x U; elim=>//=[|?->?->//|].
  by move=>???; rewrite QRegAuto.disjoint_qregC.
  move=>????? IH; rewrite QRegAuto.disjoint_qregC; f_equal.
  by under eq_forallb do rewrite IH.
- move=>? IH1 ? IH2 u2; rewrite IH1 IH2.
  elim: u2=>//=[?<-?<-|????? IH].
  - by rewrite !andbA; f_equal; rewrite -!andbA; f_equal; rewrite andbC.
  - rewrite -!andbA; f_equal; rewrite andbC -andbA; f_equal.
    by rewrite forallb_and; under eq_forallb do rewrite andbC IH.
- move=>?? x?? IH; elim=>//=.
  - by apply/forallP=>?; rewrite IH.
  - move=>???; rewrite QRegAuto.disjoint_qregC; f_equal.
    by under eq_forallb do rewrite IH/=.
  - move=>?<-?<-; rewrite -!andbA; f_equal; rewrite [RHS]andbC -andbA; f_equal.
    by rewrite forallb_and; under eq_forallb do rewrite IH/= -!IH andbC.
  - move=>????? IH1; rewrite QRegAuto.disjoint_qregC -!andbA; f_equal.
    apply/eqb_iff; split.
      move=>/andP[]/forallP P1 /forallP P2; apply/andP; split; apply/forallP=>i.
      by move: (P2 i); rewrite IH/==>/andP[].
      rewrite -IH1; apply/andP; split=>//; apply/forallP=>j.
      by move: (P2 j); rewrite !IH/==>/andP[] _ /forallP.
    move=>/andP[]/forallP P1 /forallP P2; apply/andP; split; apply/forallP=>i.
    by move: (P2 i); rewrite -IH1/==>/andP[].
    rewrite IH/=; apply/andP; split=>//; apply/forallP=>j.
    by move: (P2 j); rewrite -IH1 -IH/==>/andP[] _ /forallP.
Qed.

Lemma ucmd_disj_lockC u1 u2 : ucmd_disj_lock u1 u2 = ucmd_disj_lock u2 u1.
Proof. by rewrite -!ucmd_disj_lockE ucmd_disjC. Qed.

Ltac tac_ucmd_disj := repeat match goal with
  | [ |- forall _ , _ ] => intros; 
          rewrite /= ?(eq_qreg_fst, eq_qreg_snd, eq_qreg_tuplei, eq_qreg_ffuni)/=
  | [ H : is_true (ucmd_disj_lock ?x ?y) |- is_true (ucmd_disj_lock ?x ?y)] => 
          apply H
  | [ H : is_true (ucmd_disj_lock ?x ?y) |- is_true (ucmd_disj_lock ?y ?x)] => 
          rewrite ucmd_disj_lockC; apply H
  | [ |- is_true (ucmd_disj_lock uskip_ _)] => 
          apply/ucmd_disj_lock_uskip
  | [ |- is_true (ucmd_disj_lock (unitary_ _ _) _)] => 
          apply/ucmd_disj_lock_unitary
  | [ |- is_true (ucmd_disj_lock (sequ_ _ _) _)] => 
          apply/ucmd_disj_lock_sequ
  | [ |- is_true (ucmd_disj_lock (qcond2_ _ _ _ _) _)] => 
          apply/ucmd_disj_lock_qcond2
  | [ |- is_true (ucmd_disj_lock (qcond_ _ _ _) _)] => 
          apply/ucmd_disj_lock_qcond
  | [ |- is_true (ucmd_disj_lock (if _ then _ else _) _)] =>
          rewrite ?eqxx/=; try apply/ucmd_disj_lock_if
  | [ |- is_true (ucmd_var_disj_lock _ _) ] => tac_ucmd_var_disj
end.

(* ucmd_var_subset is still under develop *)
(* here we only provide a ltac that solve the simplest cases *)
Lemma ucmd_var_subset_lock_uskip T (x : qreg T) : 
  ucmd_var_subset_lock x uskip_.
Proof. by rewrite -ucmd_var_subset_lockE /ucmd_var_subset. Qed.

Lemma ucmd_var_subset_lock_unitary T (x : qreg T) U : 
  ucmd_var_subset_lock x (unitary_ x U).
Proof. by rewrite -ucmd_var_subset_lockE /ucmd_var_subset. Qed.

Lemma ucmd_var_subset_lock_sequ T (x : qreg T) u1 u2 :
  ucmd_var_subset_lock x u1 -> ucmd_var_subset_lock x u2 ->
  ucmd_var_subset_lock x (sequ_ u1 u2).
Proof. by rewrite -ucmd_var_subset_lockE /ucmd_var_subset/==>??; apply/fsubUsetP. Qed.

Lemma ucmd_var_subset_lock_qcond2 (x : qreg Bool) phi u0 u1 :
  ucmd_var_subset_lock x u0 -> ucmd_var_subset_lock x u1 ->
  ucmd_var_subset_lock x (qcond2_ x phi u0 u1).
Proof.
rewrite -ucmd_var_subset_lockE /ucmd_var_subset/==>??.
rewrite qcond2_.unlock/=; apply/fsubUsetP; split=>//.
by apply/bigfcupsP; case.
Qed.

Lemma ucmd_var_subset_lock_qcond T (F : finType) (x : qreg T) phi (f : F -> ucmd_) :
  (forall i, ucmd_var_subset_lock x (f i)) ->
  ucmd_var_subset_lock x (qcond_ x phi f).
Proof.
rewrite -ucmd_var_subset_lockE /ucmd_var_subset/==>P.
by apply/fsubUsetP; split=>//; apply/bigfcupsP.
Qed.

Lemma ucmd_var_subset_lock_if T (x : qreg T) b u0 u1:
  ucmd_var_subset_lock x u0 -> ucmd_var_subset_lock x u1 ->
  ucmd_var_subset_lock x (if b then u0 else u1).
Proof. by case: b. Qed.

Ltac tac_ucmd_var_subset := repeat match goal with
  | [ |- forall _ , _ ] => intros; 
          rewrite /= ?(eq_qreg_fst, eq_qreg_snd, eq_qreg_tuplei, eq_qreg_ffuni)/=
  | [ H : is_true (ucmd_var_subset_lock ?x ?y) |- is_true (ucmd_var_subset_lock ?x ?y)] =>
          apply H
  | [ |- is_true (ucmd_var_subset_lock _ uskip_)] => 
          apply/ucmd_var_subset_lock_uskip
  | [ |- is_true (ucmd_var_subset_lock _ (unitary_ _ _))] => 
          try apply/ucmd_var_subset_lock_unitary
  | [ |- is_true (ucmd_var_subset_lock _ (sequ_ _ _))] => 
          apply/ucmd_var_subset_lock_sequ
  | [ |- is_true (ucmd_var_subset_lock _ (qcond2_ _ _ _ _))] => 
          try apply/ucmd_var_subset_lock_qcond2
  | [ |- is_true (ucmd_var_subset_lock _ (qcond_ _ _ _))] => 
          try apply/ucmd_var_subset_lock_qcond
  | [ |- is_true (ucmd_var_subset_lock _ (if _ then _ else _)) ] =>
          rewrite ?eqxx/=; try apply/ucmd_var_subset_lock_if
end.

Lemma ucmd_wf_lock_uskip : ucmd_wf_lock uskip_.
Proof. by rewrite -ucmd_wf_lockE. Qed.

Lemma ucmd_wf_lock_unitary T (x : qreg T) U : 
  valid_qreg x -> ucmd_wf_lock (unitary_ x U).
Proof. by rewrite -ucmd_wf_lockE/=. Qed.

Lemma ucmd_wf_lock_sequ u1 u2 :
  ucmd_wf_lock u1 -> ucmd_wf_lock u2 ->
  ucmd_wf_lock (sequ_ u1 u2).
Proof. by rewrite -ucmd_wf_lockE/==>->->. Qed.

Lemma ucmd_wf_lock_qcond2 (x : qreg Bool) phi u0 u1 :
  ucmd_wf_lock u0 -> ucmd_wf_lock u1 ->
  ucmd_var_disj_lock x u0 -> ucmd_var_disj_lock x u1 ->
  ucmd_wf_lock (qcond2_ x phi u0 u1).
Proof.
rewrite -ucmd_wf_lockE qcond2_.unlock/= -ucmd_var_disj_lockE=>????.
by rewrite qreg_is_valid/=; apply/forallP; case; apply/andP; split.
Qed.

Lemma ucmd_wf_lock_qcond T (F : finType) (x : qreg T) phi (f : F -> ucmd_) :
  valid_qreg x ->
  (forall i, ucmd_wf_lock (f i)) -> (forall i, ucmd_var_disj_lock x (f i)) ->
  ucmd_wf_lock (qcond_ x phi f).
Proof.
rewrite -ucmd_wf_lockE /= -ucmd_var_disj_lockE ?qreg_is_valid/==>->??.
by apply/forallP=>i; apply/andP; split.
Qed.

Lemma ucmd_wf_lock_if b u0 u1:
  ucmd_wf_lock u0 -> ucmd_wf_lock u1 ->
  ucmd_wf_lock (if b then u0 else u1).
Proof. by case: b. Qed.

Ltac tac_ucmd_wf := repeat match goal with
  | [ |- forall _ , _ ] => intros
  | [ H : is_true (ucmd_wf_lock ?x) |- is_true (ucmd_wf_lock ?x)] => 
          apply H
  | [ |- is_true (ucmd_wf_lock uskip_)] => 
          apply/ucmd_wf_lock_uskip
  | [ |- is_true (ucmd_wf_lock (unitary_ _ _))] => 
          apply/ucmd_wf_lock_unitary
  | [ |- is_true (ucmd_wf_lock (sequ_ _ _))] => 
          apply/ucmd_wf_lock_sequ
  | [ |- is_true (ucmd_wf_lock (qcond2_ _ _ _ _))] => 
          apply/ucmd_wf_lock_qcond2
  | [ |- is_true (ucmd_wf_lock (qcond_ _ _ _))] => 
          apply/ucmd_wf_lock_qcond
  | [ |- is_true (ucmd_wf_lock (if _ then _ else _)) ] =>
          rewrite ?eqxx/=; try apply/ucmd_wf_lock_if
  | [ |- is_true (ucmd_var_disj_lock _ _) ] => tac_ucmd_var_disj
  | [ |- is_true (valid_qreg _) ] => QRegAuto.tac_expose
end.

Ltac tac_circuit_auto := rewrite /cmd_expose ?ucmd_var_disj_lockE
  ?ucmd_disj_lockE ?ucmd_var_subset_lockE ?ucmd_wf_lockE;
  rewrite /= ?(eq_qreg_fst, eq_qreg_snd, eq_qreg_tuplei, eq_qreg_ffuni)/=;
  match goal with
  | [ H : ?x |- ?x ] => apply H
  | [ |- forall _ , _ ] => intros; 
          rewrite /= ?(eq_qreg_fst, eq_qreg_snd, eq_qreg_tuplei, eq_qreg_ffuni)/=
  | [ |- is_true (ucmd_var_disj_lock _ _)] => tac_ucmd_var_disj
  | [ |- is_true (disjoint_qreg _ _)] => QRegAuto.tac_expose
  | [ |- is_true (ucmd_disj_lock _ _)] => tac_ucmd_disj
  | [ |- is_true (ucmd_var_subset_lock _ _)] => tac_ucmd_var_subset
  | [ |- is_true (ucmd_wf_lock _)] => tac_ucmd_wf
  | [ |- is_true (valid_qreg _)] => QRegAuto.tac_expose
  end.

Module Exports.
Global Hint Extern 0 (cmd_expose _) => (tac_circuit_auto) : typeclass_instances.

(*
Goal forall T (x : 'QReg[T]) U, `{{ucmd_wf (unitary_ x U)}}.
Proof. intros. tac_circuit_auto. Qed.

Goal forall T (x : 'QReg[T]) U, `{{ucmd_var_subset x (unitary_ x U)}}.
Proof. intros. tac_circuit_auto. Qed.

Goal forall T1 T2 (x : 'QReg[T1 * T2]) U1 U2,
  `{{ucmd_disj (unitary_ <{x.1}> U1) (unitary_ <{x.2}> U2)}}.
Proof. intros. tac_circuit_auto. Qed.

Goal forall T1 T2 (x : 'QReg[T1 * T2]) U2,
  `{{ucmd_wf (qcond_ <{x.1}> t2tv (fun i => unitary_ <{x.2}> U2))}}.
Proof. intros. tac_circuit_auto. Qed.

Goal forall T (x : 'QReg[Bool * T]) U2,
  `{{ucmd_wf (qcond2_ <{x.1}> t2tv uskip_ (unitary_ <{x.2}> U2))}}.
Proof. intros. tac_circuit_auto. Qed.

Goal forall T1 T2 (x : 'QReg[T1 * T2]) U1 U2,
  <{[ [x.1] *= U1 ; [x.2] *= U2 ]}> =u <{[ [x.2] *= U2 ; [x.1] *= U1 ]}>.
Proof. by intros; rewrite sequC. Qed. 
*)
End Exports.
End CircuitAuto.
