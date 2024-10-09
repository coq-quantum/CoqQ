From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra finmap.
From mathcomp.classical Require Import boolp classical_sets.
From mathcomp.analysis Require Import -(notations)forms topology.
From mathcomp.analysis Require Import reals normedtype sequences.
(* From mathcomp.real_closed Require Import complex. *)
From quantum.external Require Import complex.
Require Import Relation_Definitions.
Require Import -(notations)Setoid.
(* topology and setoid has notation conflicts *)
(* several lemma in classical_sets and finset have the same name. *)

Require Import mcextra mcaextra notation mxpred extnum ctopology summable.
Require Import hermitian quantum hspace hspace_extra inhabited prodvect tensor qreg qmem cpo qtype.
From quantum.dirac Require Import hstensor.
From quantum.example.qlaws Require Import basic_def circuit.
Import Order.TTheory GRing.Theory Num.Theory Num.Def HermitianTopology.
Import DefaultQMem.Exports.

Local Notation C := hermitian.C.
Local Open Scope set_scope.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope reg_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

(*****************************************************************************)
(*                 QWhile without recursive or nondeterminism                *)
(*****************************************************************************)

Inductive cmd_ : Type :=
    | skip_ 
    | abort_
    | init_      T of qreg T & 'NS('Ht T)
    | circuit_   of ucmd_
    | seqc_      of cmd_ & cmd_
    | cond_      T (f: finType) of qreg T & 'QM(f;'Ht T) & (f -> cmd_)
    | while_     T (x : qreg T) of 'QM(bool;'Ht T) & cmd_.

HB.lock
Definition cond2_ T (x : qreg T) (M : 'QM(bool; 'Ht T)) (c0 c1 : cmd_) :=
  cond_ x M (fun b => if b then c1 else c0).

Notation "'skip'" := skip_ (in custom cmd at level 0).
Notation "'abort'" := abort_ (in custom cmd at level 0).
Notation " c1 ';;' c2 " := (seqc_ c1 c2) (in custom cmd at level 30, c2 at next level, 
  left associativity, format "'[v' c1  ;;  '/' c2 ']'").
Notation "[ 'cir' c ]" := (circuit_ c) (in custom cmd at level 20,
  format "[ 'cir'  c  ]").
Notation "[ x ] ':=' v" := (init_ x v)
  (in custom cmd at level 20, x custom reg, v constr,
  format "[ x ]  ':='  v").
Notation "'If' M [ x ] '=' i 'then' F 'fI'" := (cond_ x M (fun i => F))
  (in custom cmd at level 20, x custom reg, M constr, i name, F constr,
  format "'[v' 'If'  M [ x ]  '='  i  'then'  '/' '['     F ']' '/' 'fI' ']'").
Notation "'While' M [ x ] '=' '1' 'do' c 'od'" := (while_ x M c)
  (in custom cmd at level 20, x custom reg, M constr,
  format "'[v' 'While'  M [ x ]  '='  '1'  'do'  '/' '['     c ']' '/'  'od' ']'").
Notation " c0 '◁' M [ x ] '▷' c1 " := (cond2_ x M c0 c1)
  (in custom cmd at level 20, x custom reg, M constr,
  format "c0  '◁'  M [ x ]  '▷'  c1").
Notation " c0 '◁' [ x ] '▷' c1 " := (cond2_ x bvmeas_reverse_coercion1 c0 c1)
  (in custom cmd at level 20, x custom reg, only printing,
  format "c0  '◁'  [ x ]  '▷'  c1").
Notation " c0 '◁' [ x ] '▷' c1 " := (cond2_ x bvmeas_reverse_coercion c0 c1)
  (in custom cmd at level 20, x custom reg,
  format "c0  '◁'  [ x ]  '▷'  c1").
Notation "M [ x ] '▷' c " := (cond2_ x M skip_ c)
  (in custom cmd at level 20, x custom reg,
  format "M [ x ]  '▷'  c").
Notation "[ x ] '▷' c" := (cond2_ x bvmeas_reverse_coercion1 skip_ c)
  (in custom cmd at level 20, x custom reg, only printing,
  format "[ x ]  '▷'  c").
Notation "[ x ] '▷' c" := (cond2_ x bvmeas_reverse_coercion skip_ c)
  (in custom cmd at level 20, x custom reg,
  format "[ x ]  '▷'  c").
Notation "M [ x ] '*' c " := (while_ x M c)
  (in custom cmd at level 20, x custom reg,
  format "M [ x ]  '*'  c").
Notation "[ x ] '*' c " := (while_ x bvmeas_reverse_coercion1 c)
  (in custom cmd at level 20, x custom reg, only printing,
  format "[ x ]  '*'  c").
Notation "[ x ] '*' c " := (while_ x bvmeas_reverse_coercion c)
  (in custom cmd at level 20, x custom reg,
  format "[ x ]  '*'  c").
Notation "''[' M [ x ] ]" := (cond2_ x M skip_ skip_)
  (in custom cmd at level 20, x custom reg, M constr,
  format "''['  M [ x ]  ]").
Notation "''(' M [ x ] ]" := (cond2_ x M abort_ skip_)
  (in custom cmd at level 20, x custom reg, M constr,
  format "''('  M [ x ]  ]").
Notation "''[' M [ x ] )" := (cond2_ x M skip_ abort_)
  (in custom cmd at level 20, x custom reg, M constr,
  format "''['  M [ x ]  )").
Notation "''[' M ]" := (cond2_ _ M skip_ skip_)
  (in custom cmd at level 20, M constr, only printing,
  format "''[' M ]").
Notation "''(' M ]" := (cond2_ _ M abort_ skip_)
  (in custom cmd at level 20, M constr, only printing,
  format "''(' M ]").
Notation "''[' M )" := (cond2_ _ M skip_ abort_)
  (in custom cmd at level 20, M constr, only printing,
  format "''[' M )").

Notation b0 := (choi2so (dim 'H[msys]_finset.setT)%:R%:M).
Notation setT := finset.setT.
Notation set0 := finset.set0.

Fixpoint cmd_vset u : {set mlab} :=
    match u with
    | skip_       => set0
    | abort_      => set0
    | init_  T x v => mset x
    | circuit_ u  => ucmd_vset u 
    | seqc_ c1 c2 => cmd_vset c1 :|: cmd_vset c2
    | cond_ T F x M f => mset x :|: (\bigcup_i cmd_vset (f i))
    | while_ T x M c => mset x :|: cmd_vset c 
    end.

(* Proposition 3.1 ; we use structural representation as definition *)
Fixpoint fsem_aux (c : cmd_) : 'SO[msys]_setT :=
  match c with
    | abort_            => 0
    | skip_             => \:1
    | circuit_ u        => formso (usem u)
    | init_ T x v       => liftfso (initialso (tv2v x v))
    | cond_ T F x M fc  => ifso (liftf_fun (tm2m x x M)) (fun i : F => fsem_aux (fc i))
    | while_ T x M c    => whileso (liftf_fun (tm2m x x M)) true (fsem_aux c)
    | seqc_ c1 c2     => (fsem_aux c2) :o (fsem_aux c1)
  end.
HB.lock Definition fsem := fsem_aux.

(* Definition 5.1, equivalence of programs *)
HB.lock
Definition eq_fsem u1 u2 := fsem u1 = fsem u2.
Infix "=c" := eq_fsem (at level 70).

Lemma eq_fsem_trans : 
  forall a b c, a =c b -> b =c c -> a =c c.
Proof. by rewrite eq_fsem.unlock; move=>a b c -> ->. Qed.
Lemma eq_fsem_refl : forall a, a =c a.
Proof. by rewrite eq_fsem.unlock. Qed.
Lemma eq_fsem_sym : forall a b, a =c b -> b =c a.
Proof. by rewrite eq_fsem.unlock; move=>a b ->. Qed.
Hint Extern 0 (eq_fsem _ _) => (apply eq_fsem_refl) : core.

Add Parametric Relation : cmd_ eq_fsem
  reflexivity proved by eq_fsem_refl
  symmetry proved by eq_fsem_sym
  transitivity proved by eq_fsem_trans
  as eq_fsem_rel.

(* Proposition 3.1 , Structure represantation of fsem  *)
Section fsem.

Lemma fsem_abortE : fsem <{[ abort ]}> = 0.
Proof. by rewrite fsem.unlock. Qed.

Lemma fsem_skipE : fsem <{[ skip ]}> = \:1.
Proof. by rewrite fsem.unlock. Qed.

Lemma fsem_initE T (x : qreg T) v : 
  fsem <{[ [x] := v ]}> = liftfso (initialso (tv2v x v)).
Proof. by rewrite fsem.unlock. Qed.

Lemma fsem_circuitE u : fsem <{[ [cir u ] ]}> = formso (usem u).
Proof. by rewrite fsem.unlock. Qed.

Lemma fsem_condE T (G : finType) (x : qreg T) M (fc : G -> cmd_) : 
  fsem <{[ If M[x] = i then fc i fI ]}> = 
    ifso (liftf_fun (tm2m x x M)) (fun i : G => fsem (fc i)).
Proof. by rewrite fsem.unlock. Qed.

Lemma fsem_cond2E T x M c0 c1 : fsem (@cond2_ T x M c0 c1) = 
  fsem c1 :o formso (liftf_lf (tf2f x x (M true))) + 
    (fsem c0 :o formso (liftf_lf (tf2f x x (M false)))).
Proof. by rewrite cond2_.unlock fsem_condE (ifso_bool true)/=. Qed.

Lemma fsem_whileE T (x : qreg T) M c : 
  fsem <{[ M[x] * c ]}> = whileso (liftf_fun (tm2m x x M)) true (fsem c).
Proof. by rewrite fsem.unlock. Qed.

Lemma fsem_seqE c1 c2 : fsem <{[ c1 ;; c2 ]}> = fsem c2 :o fsem c1.
Proof. by rewrite fsem.unlock. Qed.

Definition fsemE := (fsem_abortE, fsem_skipE, fsem_initE, 
  fsem_circuitE, fsem_condE, fsem_cond2E, fsem_seqE, fsem_whileE).

(* the semantics of qwhile program is a cptn map, i.e., is a quantum operation *)
Lemma fsem_qo c : fsem c \is cptn.
Proof.
elim: c.
by rewrite fsemE is_cptn.
by rewrite fsemE is_cptn.
by move=>T q v; rewrite fsemE is_cptn.
by move=>u; rewrite fsemE is_cptn.
by move=>c1 IH1 c2 IH2; rewrite fsemE (QOperation_BuildE IH1) (QOperation_BuildE IH2) is_cptn.
- move=>T x F M c IH; rewrite fsemE.
  under eq_fun do rewrite (QOperation_BuildE (IH _)).
  by apply/is_cptn.
by move=>T x M c IH; rewrite fsemE (QOperation_BuildE IH) is_cptn.
Qed.
HB.instance Definition _ c := isQOperation.Build _ _ _ (fsem_qo c).

(* the semantics of a program can be formulated locally, *)
(* i.e., fsem c = E ⊗ I for some local quantum operation E *)
Lemma fsem_local c : exists E : 'SO_(cmd_vset c), fsem c = liftfso E.
Proof.
elim: c.
by exists \:1; rewrite fsemE liftfso1.
by exists (0 : 'SO); rewrite fsemE linear0.
by move=>T q v; exists (initialso (tv2v q v)); rewrite fsemE.
- move=>u; move: (usem_local u)=>[U PU]; exists (formso U);
  by rewrite fsemE PU liftfso_formso.
- move=>c1 [E1 IH1] c2 [E2 IH2].
  exists (liftso (finset.subsetUr _ _) E2 :o liftso (finset.subsetUl _ _) E1).
  by rewrite fsemE IH1 IH2 liftfso_comp !liftfso2.
- move=>T F x M c IH.
  pose ci i : 'SO_(\bigcup_i cmd_vset (c i)) := 
    liftso (finset.bigcup_sup i is_true_true) (projT1 (cid (IH i))).
  have P3i i : fsem (c i) = liftfso (ci i)
    by rewrite /ci liftfso2; move: (projT2 (cid (IH i))).
  exists (ifso (lift_fun (finset.subsetUl _ _) (tm2m x x M)) 
      (fun i : F => liftso (finset.subsetUr _ _) (ci i))).
  rewrite fsemE liftfso_ifso liftf_fun2.
  by under [in RHS]eq_fun do rewrite liftfso2 -P3i.
- move=>T x M c [E IH].
  exists (whileso (lift_fun (finset.subsetUl _ _) (tm2m x x M)) 
    true (liftso (finset.subsetUr _ _) E)).
  move: (fsem_qo c); rewrite IH liftfso_qoE=>PE.
  by rewrite fsemE (QOperation_BuildE PE) liftfso_whileso/= liftf_fun2 liftfso2 IH. 
Qed.

(* syntactically calculate if quantum register x is disjoint from the program c *)
Fixpoint cmd_var_disj T (x : qreg T) (c : cmd_) :=
    match c with
    | skip_ | abort_ => true
    | init_ _ y _ => disjoint_qreg x y
    | circuit_ u => ucmd_var_disj x u
    | cond_ _ F y _ f => disjoint_qreg x y && [forall i : F, cmd_var_disj x (f i)]
    | while_ _ y _ c => disjoint_qreg x y && cmd_var_disj x c
    | seqc_ c1 c2 => cmd_var_disj x c1 && cmd_var_disj x c2 
    end.

(* x is syntactical disjoint from c -> the quantum systems of x and c are disjoint *)
Lemma cmd_var_disjP T (x : qreg T) (c : cmd_) :
    cmd_var_disj x c -> [disjoint mset x & cmd_vset c].
Proof.
elim: c=>/=.
1,2: by rewrite disjointX0.
by move=>???; rewrite -disj_setE.
by move=>? /ucmd_var_disj_vsetP.
by move=>? IH1 ? IH2 /andP[] /IH1 + /IH2; rewrite disjointXU=>->->.
- move=>? ? y ? fu IH /andP[] + /forallP Pi.
  rewrite disjointXU -disj_setE=>-> /=.
  by apply/bigcup_disjoint=>i _; apply/IH/Pi.
- move=>? y ? ? IH /andP[] + /IH.
  by rewrite disjointXU -disj_setE=>->->.
Qed.

(* syntactically calculate if a circuit u is disjoint from the program c *)
Fixpoint cmd_ucmd_disj (u : ucmd_) (c : cmd_) :=
    match u with
    | uskip_ => true
    | unitary_ _ y _ => cmd_var_disj y c 
    | sequ_ u1 u2 => cmd_ucmd_disj u1 c && cmd_ucmd_disj u2 c 
    | qcond_ _ F y _ fu => cmd_var_disj y c && [forall i : F, cmd_ucmd_disj (fu i) c]
    end.

(* u is syntactical disjoint from c -> the quantum systems of u and c are disjoint *)
Lemma cmd_ucmd_disjP u c :
  cmd_ucmd_disj u c -> [disjoint ucmd_vset u  & cmd_vset c].
Proof.
elim: u.
by rewrite /= disjoint0X.
by move=>???/=/cmd_var_disjP.
by move=>u1 IH1 u2 IH2/=/andP[] /IH1 + /IH2; rewrite disjointUX=>->->.
move=>?? x ? f IH /=/andP[]/cmd_var_disjP + /forallP Pi.
rewrite disjointUX=>->/=; rewrite disjoint_sym; apply/bigcup_disjoint=>i _.
by rewrite disjoint_sym; apply/IH/Pi.
Qed.

(* syntactically calculate if two programs are disjoint *)
Fixpoint cmd_disj c1 c2 :=
    match c1 with
    | skip_ | abort_     => true
    | init_ _ x _ => cmd_var_disj x c2
    | circuit_ u  => cmd_ucmd_disj u c2
    | seqc_ c11 c12 => cmd_disj c11 c2 && cmd_disj c12 c2
    | cond_ _ _ x _ f => cmd_var_disj x c2 && [forall i, cmd_disj (f i) c2]
    | while_ _ x _ c1 => cmd_var_disj x c2 && cmd_disj c1 c2
    end.

(* disjoint programs acts on disjoint systems *)
Lemma cmd_disjP c1 c2 :
    cmd_disj c1 c2 -> [disjoint cmd_vset c1 & cmd_vset c2].
Proof.
elim: c1.
1,2: by rewrite /= disjoint0X.
by move=>???/=/cmd_var_disjP.
by move=>?/=/cmd_ucmd_disjP.
by move=>? IH1 ? IH2/=/andP[]/IH1+/IH2; rewrite disjointUX=>->->.
move=>????? IH/=/andP[]/cmd_var_disjP+/forallP Pi.
rewrite disjointUX=>->/=; rewrite disjoint_sym bigcup_disjoint// =>i _;
by rewrite disjoint_sym IH.
by move=>????/= IH/andP[]/cmd_var_disjP+/IH; rewrite disjointUX=>->->.
Qed.

End fsem.

Module Export EQ_FSEM.
Require Import Setoid.

Add Parametric Morphism (T : qType) : (@init_ T )
  with signature (@eq_qreg T) ==> (@eq _) ==> eq_fsem as eq_fsem_init.
Proof.
move=>x y Pxy U; rewrite eq_fsem.unlock !fsemE -(tv2v_eqr _ Pxy).
by move: (mset_eqr default_qmemory Pxy)=>P; case: _ / P; rewrite casths_id.
Qed.

(*---------------------------------------------------------------------------*)
(*                     Lemma 5.1 (Congruence - Lifting law)                  *)
(* It is states as a relation morphism, and this allows to directly rewrite  *)
(*                 [cir u]  ==>  [cir u']    if   u =u u'                    *)
(* and thus allows to substitut in all composition of circuit in qwhile      *)
(*---------------------------------------------------------------------------*)
Add Parametric Morphism : circuit_
  with signature eq_usem ==> eq_fsem as eq_fsem_circuit.
Proof. by move=>x y; rewrite eq_fsem.unlock !fsemE eq_usem.unlock=>->. Qed.

Add Parametric Morphism : seqc_
  with signature eq_fsem ==> eq_fsem ==> eq_fsem as eq_fsem_seqc.
Proof. by rewrite eq_fsem.unlock=>??+??+; rewrite !fsemE=>->->. Qed.

Add Parametric Morphism (T : qType) (F : finType) : (@cond_ T F)
  with signature (@eq_qreg T) ==> (@eq _) ==> (@eq _) ==> eq_fsem as eq_fsem_cond.
Proof.
move=>x y Pxy M f; rewrite eq_fsem.unlock !fsemE.
by f_equal; apply/funext=>i; rewrite !liftf_funE !tm2mE 
  -(tf2f_eqr _ Pxy Pxy) liftf_lf_cast.
Qed.

Add Parametric Morphism T : (@cond2_ T)
  with signature (@eq_qreg T) ==> (@eq _) ==> eq_fsem ==> eq_fsem ==> eq_fsem
    as eq_fsem_cond2.
Proof.
move=>x y Pxy M c00 c01 + c10 c11 +.
by rewrite eq_fsem.unlock !fsemE -!(tf2f_eqr _ Pxy Pxy) !liftf_lf_cast=>->->.
Qed.

Add Parametric Morphism (T : qType) : (@while_ T)
  with signature (@eq_qreg T) ==> (@eq _) ==> eq_fsem ==> eq_fsem
    as eq_fsem_while.
Proof.
move=>x y Pxy M c1 c2; rewrite eq_fsem.unlock !fsemE=>->.
by f_equal; apply/funext=>i; rewrite !liftf_funE !tm2mE 
  -(tf2f_eqr _ Pxy Pxy) liftf_lf_cast.
Qed.

Lemma uskip_skip : <{[ [cir uskip] ]}> =c <{[ skip ]}>.
Proof. by rewrite eq_fsem.unlock !fsemE/= !usemE formso1. Qed.

Lemma eq_cond (T : qType) (x : qreg T) (F : finType) (M1 M2 : 'QM(F; 'Ht T))
  (f1 f2 : F -> cmd_) :
  (forall i, M1 i = M2 i) -> (forall i, f1 i =c f2 i) -> 
    <{[ If M1[x] = i then f1 i fI ]}> =c <{[ If M2[x] = i then f2 i fI ]}>.
Proof.
rewrite eq_fsem.unlock=>PM Pf; rewrite !fsemE; under eq_fun do rewrite Pf.
do 3 f_equal. by apply/funext.
Qed.

Lemma eq_condl (T : qType) (x : qreg T) (F : finType) (M1 M2 : 'QM(F; 'Ht T))
  (f: F -> cmd_) :
  (forall i, M1 i = M2 i) -> 
    <{[ If M1[x] = i then f i fI ]}> =c <{[ If M2[x] = i then f i fI ]}>.
Proof. by move=>/eq_cond; apply. Qed.

Lemma eq_condr (T : qType) (x : qreg T) (F : finType) (M : 'QM(F; 'Ht T))
  (f1 f2 : F -> cmd_) :
  (forall i, f1 i =c f2 i) -> 
    <{[ If M[x] = i then f1 i fI ]}> =c <{[ If M[x] = i then f2 i fI ]}>.
Proof. by move=>/eq_cond; apply. Qed.

Lemma eq_cond2 T (x : qreg T) (M1 M2 : 'QM) c0 c1 :
  (forall i, M1 i = M2 i) -> 
     <{[ c0 ◁ M1[x] ▷ c1 ]}> =c <{[ c0 ◁ M2[x] ▷ c1 ]}>.
Proof. by rewrite cond2_.unlock; exact: eq_condl. Qed.

Lemma seqc_circuit u1 u2 : 
  <{[ [cir u1 ; u2 ] ]}> =c <{[ ([cir u1 ]) ;; ([cir u2 ]) ]}>.
Proof. by rewrite eq_fsem.unlock !fsemE usemE formso_comp. Qed.

(* easier for use *)
Lemma seqc_circuitA c u1 u2 : 
  <{[ c ;; [cir u1 ; u2 ] ]}> =c <{[ c ;; ([cir u1 ]) ;; [cir u2 ] ]}>.
Proof. by rewrite seqc_circuit eq_fsem.unlock !fsemE comp_soA. Qed.

Lemma eq_init (T : qType) (x : qreg T) (v1 v2 : 'NS('Ht T)) :
  v1 = v2 :> 'Ht T -> <{[ [x] := v1 ]}> =c <{[ [x] := v2 ]}>.
Proof. by move=>Pv; rewrite eq_fsem.unlock !fsemE/= Pv. Qed.

Lemma eq_while (T : qType) (x : qreg T) (M1 M2 : 'QM) c :
  (forall i, M1 i = M2 i) -> <{[ M1[x] * c ]}> =c <{[ M2[x] * c ]}>.
Proof.
move=>P; rewrite eq_fsem.unlock !fsemE; do 3 f_equal.
by apply/funext.
Qed.

Lemma eq_seqcl u1 u2 u3 :
  u1 =c u2 -> <{[ u1 ;; u3 ]}> =c <{[ u2 ;; u3 ]}>.
Proof. by move=>->. Qed.

Lemma eq_seqcr u1 u2 u3 :
  u1 =c u2 -> <{[ u3 ;; u1 ]}> =c <{[ u3 ;; u1 ]}>.
Proof. by move=>->. Qed.

Lemma eq_seqc u1 u2 u3 u4 :
  u1 =c u2 -> u3 =c u4 -> <{[ u1 ;; u3 ]}> =c <{[ u2 ;; u4 ]}>.
Proof. by move=>->->. Qed.

End EQ_FSEM.

Section QWhileLaw.

(* proposition 5.1 (1) : initialization law, cancellation *)
Lemma init_seqcK T (x : 'QReg[T]) (phi psi : 'NS('Ht T)) :
  <{[ ([x] := phi) ;; ([x] := psi) ]}> =c <{[ [x] := psi ]}>.
Proof.
rewrite eq_fsem.unlock !fsemE -liftfso_comp; f_equal; apply/superopP =>y.
by rewrite soE !initialsoE linearZ/= outp_trlf tv2v_dot ns_dot mulr1.
Qed.

(* proposition 5.1 (2) : initialization law, unitary-elimination *)
Lemma init_circuitK T (x : 'QReg[T]) phi (u : ucmd_) (sc : 'FU('Ht T)) :
  usem u = liftf_lf (tf2f x x sc) -> 
    <{[ ([x] := phi) ;; ([cir u ]) ]}> =c 
      <{[ [x] := NormalState.clone _ (sc (phi : 'Ht T)) _]}>.
Proof.
rewrite eq_fsem.unlock !fsemE /==>->; rewrite -liftfso_formso -liftfso_comp.
by f_equal; apply/superopP =>y; rewrite soE !initialsoE formsoE 
  linearZr/= linearZl/= outp_compr outp_compl adjfK tf2f_apply.
Qed.

Lemma init_unitaryK T (x : 'QReg[T]) phi (u : 'FU('Ht T)) :
    <{[ ([x] := phi) ;; ([cir [x] *= u ]) ]}> =c 
      <{[ [x] := NormalState.clone _ (u (phi : 'Ht T)) _ ]}>.
Proof. by rewrite -(init_circuitK _ (u := <{[ [x] *= u ]}>))// usemE. Qed.

Lemma init_unitaryKP T (x : 'QReg[T]) (phi v : 'NS) (u : 'FU('Ht T)) :
  v = u (phi : 'Ht T) :> 'Ht T ->
    <{[ ([x] := phi) ;; ([cir [x] *= u ]) ]}> =c <{[ [x] := v ]}>.
Proof. by move=>P; rewrite init_unitaryK; apply eq_init. Qed.

(* proposition 5.1 (3) : initialization law, qif-elimination *)
Lemma init_qifTK (x : qreg Bool) (psi : 'NS('Ht Bool)) 
  (phi : 'ONB(bool; 'Ht Bool)) c0 c1 {H : `{{ucmd_var_disj x c1}}} :
  [< (psi : 'Ht _) ; phi false >] = 0 ->
    <{[ ([x] := psi) ;; ([cir c0 ← phi[x] → c1 ]) ]}> =c 
      <{[ ([x] := phi true) ;; ([cir c1 ]) ]}>.
Proof.
rewrite eq_fsem.unlock !fsemE usemE=>P1.
apply/superopP=>y; rewrite !soE.
set phi1 := liftf_lf _. set phi0 := liftf_lf _.
have ->: phi1 \o usem c1 = usem c1 \o phi1.
  by move: (usem_local c1)=>[U ->]; rewrite liftf_lf_compC// ucmd_var_disj_vsetP.
rewrite -[_ \o phi1]comp_lfunA.
have ->: phi1 \o phi1 = phi1
  by rewrite -liftf_lf_comp tf2f_comp outp_comp onb_dot eqxx scale1r.
rewrite !comp_lfunDl adjfD !comp_lfunDr !adjf_comp !comp_lfunA.
have -> : phi1^A = phi1 by rewrite -liftf_lf_adj tf2f_adj adj_outp.
have -> : phi0^A = phi0 by rewrite -liftf_lf_adj tf2f_adj adj_outp.
have P2 : forall A : 'F[msys]_setT, A \o liftfso (initialso (tv2v x psi)) y \o phi0 = 0.
  move=>A; rewrite liftfso_krausso kraussoE/= -comp_lfunA linear_suml/= big1 ?comp_lfun0r// =>i _.
  by rewrite liftf_funE -liftf_lf_adj -!comp_lfunA -liftf_lf_comp 
    adj_outp -tv2v_out outp_comp tv2v_dot P1 scale0r linear0 !comp_lfun0r.
rewrite !P2 !comp_lfun0l !addr0 -[RHS]addr0; f_equal.
f_equal; rewrite -!comp_lfunA; f_equal; rewrite !liftfso_krausso 
  !kraussoE linear_suml linear_sumr; apply eq_bigr=>i _ /=.
rewrite !liftf_funE -!liftf_lf_adj !adj_outp !comp_lfunA -comp_lfunA -!liftf_lf_comp -!tv2v_out
  !outp_comp !tv2v_dot !(linearZ, linearZl, linearZr)/= scalerA -[RHS]scale1r.
  f_equal. rewrite -(ns_dot psi).
  by rewrite {3}(onb_vec phi psi) big_bool/= dotpDl !dotpZl/= !conj_dotp P1 mul0r addr0 mulrC.
rewrite [X in X \o _]comp_lfunACA.
set t := _ \o liftfso _ _; have ->: t = 0.
rewrite /t liftfso_krausso kraussoE linear_sumr/= big1// =>i _.
  by rewrite liftf_funE !comp_lfunA -liftf_lf_comp -tv2v_out 
    outp_comp tv2v_dot -conj_dotp P1 conjC0 scale0r linear0 !comp_lfun0l.
by rewrite comp_lfun0r !comp_lfun0l.
Qed.

Lemma init_qifTK1 (x : qreg Bool) (psi : 'NS('Ht Bool)) 
  (phi : 'ONB(bool; 'Ht Bool)) c0 c1 {H : `{{ucmd_var_disj x c1}}} :
  [< (psi : 'Ht _) ; phi false >] = 0 ->
    <{[ ([x] := psi) ;; ([cir c0 ← phi[x] → c1 ]) ]}> =c 
      <{[ ([x] := psi) ;; ([cir c1 ]) ]}>.
Proof.
move=>P; rewrite init_qifTK//; apply eq_seqcl.
rewrite eq_fsem.unlock !fsemE; f_equal; apply/superopP=>r.
rewrite !initialsoE; f_equal; rewrite !tv2v_out; f_equal.
move: (onb_vec phi psi); rewrite big_bool/= -[[< phi false; _>]]conj_dotp P conjC0 scale0r addr0=>P1.
move: {+}P1=>/(f_equal normr); rewrite normrZ !ns_norm mulr1=>P2.
by rewrite P1 outpZl outpZr scalerA -normCK -P2 expr1n scale1r.
Qed.

Lemma init_qifFK (x : qreg Bool) (psi : 'NS('Ht Bool)) 
  (phi : 'ONB(bool; 'Ht Bool)) c0 c1 {H : `{{ucmd_var_disj x c0}}} :
  [< (psi : 'Ht _) ; phi true >] = 0 ->
    <{[ ([x] := psi) ;; ([cir c0 ← phi[x] → c1 ]) ]}> =c 
      <{[ ([x] := phi false) ;; ([cir c0 ]) ]}>.
Proof.
move=>P; rewrite qif_sym init_qifTK//=.
by apply/eq_seqcl/eq_init.
Qed.

(* proposition 5.1 (4) : initialization law, if-elimination *)
Lemma init_ifTK T (x : 'QReg[T]) (psi : 'NS('Ht T)) c0 c1 :
  let M := '[| psi >] in
  <{[ ([x] := psi) ;; (c0 ◁ M[x] ▷ c1) ]}> =c 
    <{[ ([x] := psi) ;; c1 ]}>.
Proof.
rewrite /= eq_fsem.unlock !fsemE linearDl/= -!comp_soA 
  -!liftfso_formso -!liftfso_comp -[RHS]addr0; do ! f_equal.
apply/superopP=>y. rewrite soE initialsoE formsoE linearZr/= linearZl/=; f_equal.
by rewrite tf2f_adj adj_outp tv2v_out !tf2f_comp 
  outp_comp ns_dot scale1r outp_comp ns_dot scale1r.
set t := formso _ :o _; suff ->: t = 0 by rewrite linear0 comp_so0r.
by apply/superopP=>y; rewrite /t soE initialsoE !soE linearZr/= tv2v_out tf2f_comp 
  linearBl/= outp_comp ns_dot scale1r comp_lfun1l subrr linear0 scaler0 comp_lfun0l.
Qed.

Lemma init_ifFK (x : qreg Bool) (phi psi : 'NS('Ht Bool)) c0 c1 :
  [< (phi : 'Ht _); (psi : 'Ht _) >] = 0 ->
  let M := '[| psi >] in
  <{[ ([x] := phi) ;; (c0 ◁ M[x] ▷ c1) ]}> =c 
    <{[ ([x] := phi) ;; c0 ]}>.
Proof.
move=>P; rewrite /= eq_fsem.unlock !fsemE linearDl/= 
  -!comp_soA -!liftfso_formso -!liftfso_comp -[RHS]add0r.
do ! f_equal.
set t := formso _ :o _; suff ->: t = 0 by rewrite linear0 comp_so0r.
by apply/superopP=>y; rewrite /t soE initialsoE !soE linearZr/= tv2v_out
  tf2f_comp outp_comp -conj_dotp P conjC0 scale0r linear0 scaler0 comp_lfun0l.
apply/superopP=>y. rewrite soE initialsoE formsoE linearZr/= linearZl/=; f_equal.
by rewrite tf2f_adj adjfB adjf1 adj_outp -!tf2fB tf2f1 tv2v_out linearBl/= 
  tf2f_comp outp_comp -conj_dotp P conjC0 scale0r tf2f0 subr0 comp_lfun1l 
  linearBr/= tf2f_comp outp_comp P scale0r tf2f0 subr0 comp_lfun1r.
Qed.

(* proposition 5.1 (5) : if Expansion *)
(* for simplicity, we focus on the simple case of r, i.e., r = (q1, q2) *)
(*   other type structures are in principle the same *)
Lemma if_expansion T1 T2 (x1 : 'QReg[T1]) (x2 : 'QReg[T2]) 
  (P : evalQT T1 -> cmd_) (phi : 'NS('Ht (T1 * T2))) {Hx : `{{disjoint_qreg x1 x2}}}
  {H : `{{forall i, cmd_var_disj <{(x1,x2)}> (P i)}}} :
    <{[ If tmeas[x1] = m then P m fI ;; [(x1,x2)] := phi ]}> =c
      <{[ If tmeas[(x1,x2)] = k then P k.1 fI ;; [(x1,x2)] := phi ]}>.
Proof.
move: Hx; rewrite /cmd_expose=>Hx.
rewrite eq_fsem.unlock !fsemE !ifso_elem pair_bigV/= !linear_sumr/=.
apply eq_bigr; rewrite -/evalQT=>i _.
rewrite -linear_sumr/= !comp_soA.
move: (fsem_local (P i))=>[E ->]; rewrite liftfso_compC ?cmd_var_disjP//.
rewrite -!comp_soA; f_equal.
transitivity (liftfso (initialso (tv2v <{(x1, x2)}> phi)) :o 
  formso (liftf_lf (tf2f  <{(x1, x2)}> <{(x1, x2)}> ([> ''i ; '' i <] ⊗f \1)))).
by rewrite /elemso liftf_funE -tf2f_pair liftf_lf_cast tf2f1 liftf_lf_tenf1r -?disj_setE.
under eq_bigr do rewrite /elemso liftf_funE -liftfso_formso.
rewrite -linear_sum/= -liftfso_formso -!liftfso_comp; f_equal.
rewrite -(initialso_onb (tv2v <{ (x1, x2) }> phi) (tv2v_fun _ <{ (x1, x2) }> t2tv)).
rewrite -elemso_sum !linear_suml/=; apply eq_bigr=>[[j1 j2]] _.
rewrite /elemso linear_sumr/= (bigD1 j2)//= big1=>[k /negPf nkj|];
rewrite !formso_comp tm2mE tmeasE /tv2v_fun tv2v_out !tf2f_comp outp_comp.
by rewrite -!tentv_t2tv tentv_dot !t2tv_dot [_ == k]eq_sym nkj mulr0 scale0r tf2f0 formso0.
rewrite addr0; do 2 f_equal.
rewrite -(sumonb_out t2tv) tentf_sumr linear_sumr/= (bigD1 j2)//= big1=>[k /negPf nkj|];
by rewrite tentv_out ?addr0 outp_comp -!tentv_t2tv// 
  tentv_dot !t2tv_dot [_ == k]eq_sym nkj mulr0 scale0r.
Qed.

(* proposition 5.2 (1) : if statement law, truth-falsity *)
Lemma ifTK T (x : qreg T) c0 c1 :
  <{[ c0 ◁ M_T[x] ▷ c1 ]}> =c c1.
Proof.
by rewrite eq_fsem.unlock fsemE tf2f1 tf2f0 liftf_lf1 
  linear0 formso0 comp_so0r addr0 formso1 comp_so1r.
Qed.

Lemma ifFK T (x : qreg T) c0 c1 :
  <{[ c0 ◁ M_F[x] ▷ c1 ]}> =c c0.
Proof.
by rewrite eq_fsem.unlock fsemE tf2f1 tf2f0 liftf_lf1 
  linear0 formso0 comp_so0r add0r formso1 comp_so1r.
Qed.

(* proposition 5.2 (2) : if statement law, idempotence *)
Lemma if_idem T (x : qreg T) M c : 
  <{[ c ◁ M[x] ▷ c ]}> =c <{[ '[ M[x] ] ;; c ]}>.
Proof. by rewrite eq_fsem.unlock !fsemE !comp_so1l comp_soDr. Qed.

(* proposition 5.2 (3) : if statement law, complementation *)
Lemma if_compl T (x : qreg T) (M : 'QM(bool;'Ht T)) c0 c1 :
  <{[ c0 ◁ M ^m⟂[x] ▷ c1 ]}> =c <{[ c1 ◁ M[x] ▷ c0 ]}>.
Proof. by rewrite eq_fsem.unlock !fsemE addrC. Qed.

(* proposition 5.2 (4) : if statement law, associativity *)
Lemma if_projKr T (x : 'QReg[T]) (P : {hspace 'Ht T}) c0 c1 c2 :
  let M := pmeas P in
  <{[ c0 ◁ M[x] ▷ (c1 ◁ M[x] ▷ c2) ]}> =c <{[ c0 ◁ M[x] ▷ c2 ]}>.
Proof.
rewrite /= eq_fsem.unlock !fsemE; f_equal.
by rewrite linearDl/= -!comp_soA !formso_comp -!liftf_lf_comp !tf2f_comp
  projf_idem /pmeas hsE/= projf_cplmtMl !linear0 formso0 comp_so0r addr0.
Qed.

Lemma if_projKl T (x : 'QReg[T]) (P : {hspace 'Ht T}) c0 c1 c2 :
  let M := pmeas P in
  <{[ (c0 ◁ M[x] ▷ c1) ◁ M[x] ▷ c2 ]}> =c <{[ c0 ◁ M[x] ▷ c2 ]}>.
Proof.
rewrite /= eq_fsem.unlock !fsemE; f_equal.
by rewrite linearDl/= -!comp_soA !formso_comp -!liftf_lf_comp !tf2f_comp
  projf_idem /pmeas hsE/= projf_cplmtMr !linear0 formso0 comp_so0r add0r.
Qed.

Lemma if_projA T (x : 'QReg[T]) (P : {hspace 'Ht T}) c0 c1 c2 :
  let M := pmeas P in
  <{[ c0 ◁ M[x] ▷ (c1 ◁ M[x] ▷ c2) ]}> =c 
    <{[ (c0 ◁ M[x] ▷ c1) ◁ M[x] ▷ c2 ]}>.
Proof. by rewrite /= if_projKr if_projKl. Qed.

(* proposition 5.2 (5) : if statement law, if elimination *)
Lemma if_entail T (x : 'QReg[T]) (M N K : 'QM) c0 c1 :
  M ▶ N -> K ≅ M & N ->
    <{[ '( M[x] ] ;; (c0 ◁ N[x] ▷ c1) ]}> =c <{[ '( K[x] ] ;; c1 ]}>.
Proof.
move=>P1 P2; rewrite eq_fsem.unlock !fsemE !comp_so1l !comp_so0l !addr0
  linearDl/= -!comp_soA !formso_comp -!liftf_lf_comp !tf2f_comp P1.
rewrite tf2f0 linear0 formso0 comp_so0r addr0; f_equal.
move: P2=>[c Pc] /(f_equal (fun x=> c^-1 *: x)).
rewrite scalerA mulVf -1?normr_eq0 ?Pc ?oner_neq0// scale1r=><-.
by rewrite !linearZ/= formso_eqZ// normfV Pc invr1.
Qed.

Lemma if_weaker T (x : 'QReg[T]) (M N : 'QM) c1 c2 c3 :
  M ∝ N -> <{[ c1 ◁ N[x] ▷ (c2 ◁ M[x] ▷ c3) ]}> =c <{[ c1 ◁ N[x] ▷ c3 ]}>.
Proof.
move=>/meas_weakerP[] [c Pc P2] P1.
rewrite eq_fsem.unlock !fsemE; f_equal.
rewrite comp_soDl -!comp_soA !formso_comp -!liftf_lf_comp 
  !tf2f_comp P1 tf2f0 linear0 formso0 comp_so0r addr0; f_equal.
by rewrite P2 !linearZ/=; apply formso_eqZ.
Qed.

Lemma if_weakerrl T (x : 'QReg[T]) (M N : 'QM) c1 c2 c3 :
  M ^m⟂ ∝ N -> <{[ c1 ◁ N[x] ▷ (c2 ◁ M[x] ▷ c3) ]}> =c <{[ c1 ◁ N[x] ▷ c2 ]}>.
Proof. by move=>P; rewrite -[X in cond2_ _ _ _ X]if_compl if_weaker. Qed.

Lemma if_weakerll T (x : 'QReg[T]) (M N : 'QM) c1 c2 c3 :
  M ^m⟂ ∝ N ^m⟂ -> <{[ (c1 ◁ M[x] ▷ c2) ◁ N[x] ▷ c3 ]}> =c <{[ c1 ◁ N[x] ▷ c3 ]}>.
Proof. by move=>P; rewrite -if_compl if_weakerrl// if_compl. Qed.  

Lemma if_weakerlr T (x : 'QReg[T]) (M N : 'QM) c1 c2 c3 :
  M ∝ N ^m⟂ -> <{[ (c1 ◁ M[x] ▷ c2) ◁ N[x] ▷ c3 ]}> =c <{[ c2 ◁ N[x] ▷ c3 ]}>.
Proof. by move=>P; rewrite -if_compl if_weaker// if_compl. Qed.  

(* Lemma 5.2 *)
Lemma meas_reducel T (x : 'QReg[T]) (N : 'QM) (M : 'QM) (K : 'QM) (L : 'QM) :
  <{[ '[ N[x] ) ]}> =c <{[ '[ K[x] ) ◁ M[x] ▷ '[ L[x] ) ]}> <->
    exists (c0 c1 : C), (c0^+2 + c1^+2 = 1) /\ 
    ((K false \o M false) ⋈_(c0) (N false)) /\ ((L false \o M true) ⋈_(c1) (N false)).
Proof.
rewrite meas_proportionP; split.
  move=>+ r; rewrite eq_fsem.unlock !fsemE !comp_so0l !comp_so1l !add0r.
  move/superopP=>/(_ (liftf_lf (tf2f x x r))).
  rewrite !soE -!liftf_lf_adj -!liftf_lf_comp !tf2f_adj !tf2f_comp -!linearD/=;
  by move=>/liftf_lf_inj/tf2f_inj->; rewrite addrC !adjf_comp !comp_lfunA.
move=>P; rewrite eq_fsem.unlock !fsemE !comp_so0l !comp_so1l !add0r.
rewrite -!liftfso_formso -!liftfso_comp -linearD/=; f_equal.
apply/superopP=>r; rewrite -(f2tfK r); set r' := f2tf r.
by rewrite !soE !tf2f_adj !tf2f_comp -linearD/= -P addrC !adjf_comp !comp_lfunA.
Qed.

Lemma meas_reducer T (x : 'QReg[T]) (N : 'QM) (M : 'QM) (K : 'QM) (L : 'QM) :
  <{[ '( N[x] ] ]}> =c <{[ '( K[x] ] ◁ M[x] ▷ '( L[x] ] ]}> <->
    exists (c0 c1 : C), (c0^+2 + c1^+2 = 1) /\ 
    ((K true \o M false) ⋈_(c0) (N true)) /\ ((L true \o M true) ⋈_(c1) (N true)).
Proof. by rewrite -![ cond2_ _ _ abort_ _]if_compl meas_reducel/= !/bcmeas/=. Qed.

Lemma meas_aborbl T (x : 'QReg[T]) (N : 'QM) (M : 'QM) :
  <{[ '[ N[x] ) ]}> =c <{[ '[ M[x] ] ;; '[ N[x] ) ]}> <->
    exists (c0 c1 : C), (c0^+2 + c1^+2 = 1) /\ 
    (N false ⋊_(c0) M false) /\ (N false ⋊_(c1) M true).
Proof.
rewrite meas_aborb; split.
  move=>+ r; rewrite eq_fsem.unlock !fsemE !comp_so0l !comp_so1l !add0r.
  move/superopP=>/(_ (liftf_lf (tf2f x x r))).
  rewrite !soE -!liftf_lf_adj !tf2f_adj -!liftf_lf_comp 
    !tf2f_comp -!linearD/= -!liftf_lf_comp !tf2f_comp.
  by move=>/liftf_lf_inj/tf2f_inj->; rewrite addrC !linearDr/= linearDl/= !comp_lfunA.
move=>P; rewrite eq_fsem.unlock !fsemE !comp_so0l !comp_so1l !add0r.
rewrite -!liftfso_formso -linearD -!liftfso_comp; f_equal.
apply/superopP=>r; rewrite -(f2tfK r); set r' := f2tf r.
by rewrite !soE !tf2f_adj !tf2f_comp -linearD/= 
  !tf2f_comp linearDr/= linearDl/= -P addrC !comp_lfunA.
Qed.

Lemma meas_aborbr T (x : 'QReg[T]) (N : 'QM) (M : 'QM) :
  <{[ '( N[x] ] ]}> =c <{[ '[ M[x] ] ;; '( N[x] ] ]}> <->
    exists (c0 c1 : C), (c0^+2 + c1^+2 = 1) /\ 
    (N true ⋊_(c0) M false) /\ (N true ⋊_(c1) M true).
Proof. by rewrite -![ cond2_ _ _ abort_ _]if_compl meas_aborbl/= !/bcmeas/=. Qed.

(* proposition 5.3 (1) : nested if statement law, reduction *)
Lemma if_reduce T1 T2 T3 T4 (x1 : qreg T1) (x2 : qreg T2) (x3 : qreg T3)
  (x4 : qreg T4) (N : 'QM) (M : 'QM) (K : 'QM) (L : 'QM) c0 c1 :
  <{[ '( N[x1] ] ]}> =c <{[ '( K[x3] ] ◁ M[x2] ▷ '( L[x4] ] ]}> ->
  <{[ '[ N[x1] ) ]}> =c <{[ '[ K[x3] ) ◁ M[x2] ▷ '[ L[x4] ) ]}> ->
  <{[ (c0 ◁ K[x3] ▷ c1) ◁ M[x2] ▷ (c0 ◁ L[x4] ▷ c1) ]}> =c <{[ c0 ◁ N[x1] ▷ c1 ]}>.
Proof.
rewrite eq_fsem.unlock !fsemE !comp_so1l !comp_so0l !addr0 !add0r.
by move=>->->; rewrite !linearDl/= addrACA -!comp_soA -!linearDr/=.
Qed.

Lemma if_reduce_tmeas T1 T2 (x1 : qreg T1) (x2 : qreg T2) 
  (P : evalQT T1 -> evalQT T2 -> cmd_) {H : `{{disjoint_qreg x1 x2}}} :
  <{[ If tmeas[x1] = m then <{[ If tmeas[x2] = n then P m n fI ]}> fI  ]}> 
  =c <{[ If tmeas[(x1,x2)] = k then P k.1 k.2 fI ]}>.
Proof.
rewrite eq_fsem.unlock !fsemE !ifso_elem.
under eq_bigr do rewrite fsemE ifso_elem linear_suml/=.
rewrite pair_big/=; apply eq_bigr=>[[m n]] _ /=.
rewrite -comp_soA; f_equal.
rewrite /elemso !liftf_funE !tm2mE formso_comp !tmeasE -tentv_t2tv 
  -tentv_out -tf2f_pair liftf_lf_cast liftf_lf_compC ?liftf_lf_compT//.
by rewrite disjoint_sym -disj_setE. by rewrite -disj_setE.
Qed.

(* proposition 5.3 (2) : nested if statement law, left-distributivity *)
Lemma if_distrr T (x : 'QReg[T]) (N M : 'QM) c0 c1 c2 :
  M ◇L N -> <{[ '[ N[x] ) ]}> =c <{[ '[ M[x] ] ;; '[ N[x] ) ]}> ->
    <{[ c0 ◁ N[x] ▷ (c1 ◁ M[x] ▷ c2) ]}> =c 
      <{[ (c0 ◁ N[x] ▷ c1) ◁ M[x] ▷ (c0 ◁ N[x] ▷ c2) ]}>.
Proof.
rewrite eq_fsem.unlock !fsemE !comp_so1l !comp_so0l !add0r=>[[]]P1 P2 {1}->.
rewrite !linearDl/= addrACA -linearDr/= -!comp_soA; do 3 f_equal;
by rewrite !formso_comp -!liftf_lf_comp !tf2f_comp ?P1 ?P2.
Qed.

(* proposition 5.3 (3) : nested if statement law, right-distributivity *)
Lemma if_distrl T (x : 'QReg[T]) (N M : 'QM) c0 c1 c2 :
  M ◇R N -> <{[ '( N[x] ] ]}> =c <{[ '[ M[x] ] ;; '( N[x] ] ]}> ->
    <{[ (c0 ◁ M[x] ▷ c1) ◁ N[x] ▷ c2 ]}> =c 
      <{[ (c0 ◁ N[x] ▷ c2) ◁ M[x] ▷ (c1 ◁ N[x] ▷ c2) ]}>.
Proof.
rewrite eq_fsem.unlock !fsemE !comp_so1l !comp_so0l !addr0=>[[]]P1 P2 {1}->.
rewrite !linearDl/= addrACA -linearDr/= -!comp_soA; do 3 f_equal;
by rewrite !formso_comp -!liftf_lf_comp !tf2f_comp ?P1 ?P2.
Qed.

(* proposition 5.3 (4) : nested if statement law, left-distributivity for projection *)
Lemma if_proj_distrr T (x : 'QReg[T]) (X Y : {hspace 'Ht T}) c0 c1 c2 :
  pmeas X ▶ pmeas Y \/ pmeas (~` X)%HS ▶ pmeas Y ->
    <{[ c0 ◁ pmeas Y[x] ▷ (c1 ◁ pmeas X [x] ▷ c2) ]}> =c 
      <{[ (c0 ◁ pmeas Y[x] ▷ c1) ◁ pmeas X[x] ▷ (c0 ◁ pmeas Y[x] ▷ c2) ]}>.
Proof.
move=>P; apply: if_distrr.
by case: P=>/pmeas_entail_lcom //; rewrite -pmeas_lcomOx.
rewrite eq_fsem.unlock !fsemE comp_so0l !comp_so1l add0r -!liftfso_formso -linearD/= -liftfso_comp.
f_equal; apply/superopP=>r; rewrite !soE linearDr linearDl/= !tf2f_adj !comp_lfunA !tf2f_comp.
case: P; rewrite pmeas_entailP; first rewrite -lehO.
all: move=>P1; move: P1 {+}P1.
rewrite {1}leh_compl0 leh_compl hsOK /pmeas=>/eqP->/eqP P1.
by rewrite linear0 !linear0l add0r P1 -!comp_lfunA tf2f_comp -adjf_comp P1.
rewrite {1}leh_compr0 lehOx leh_compl /pmeas=>/eqP->/eqP P1.
by rewrite linear0 !linear0l addr0 P1 -!comp_lfunA tf2f_comp -adjf_comp P1.
Qed.

(* proposition 5.3 (5) : nested if statement law, right-distributivity for projection *)
Lemma if_proj_distrl T (x : 'QReg[T]) (X Y : {hspace 'Ht T}) c0 c1 c2 :
  pmeas Y ▶ pmeas X \/ pmeas Y ▶ pmeas (~` X)%HS ->
    <{[ (c0 ◁ pmeas X[x] ▷ c1) ◁ pmeas Y[x] ▷ c2 ]}> =c 
      <{[ (c0 ◁ pmeas Y[x] ▷ c2) ◁ pmeas X[x] ▷ (c1 ◁ pmeas Y[x] ▷ c2) ]}>.
Proof.
move=>P1; rewrite -![ cond2_ _ (pmeas _) _ _]if_compl !pmeasO_qmE; apply/if_proj_distrr.
by rewrite -2!pmeas_entailO.
Qed.

(* proposition 5.4 (1) : sequential composition, unit and zero *)
Lemma skipIx c : <{[ skip ;; c ]}> =c c.
Proof. by rewrite eq_fsem.unlock !fsemE comp_so1r. Qed.

Lemma skipxI c : <{[ c ;; skip ]}> =c c.
Proof. by rewrite eq_fsem.unlock !fsemE comp_so1l. Qed.

Lemma skipC c : <{[ skip ;; c ]}> =c <{[ c ;; skip ]}>.
Proof. by rewrite skipIx skipxI. Qed.

Lemma abortIx c : <{[ abort ;; c ]}> =c <{[ abort ]}>.
Proof. by rewrite eq_fsem.unlock !fsemE comp_so0r. Qed.

Lemma abortxI c : <{[ c ;; abort ]}> =c <{[ abort ]}>.
Proof. by rewrite eq_fsem.unlock !fsemE comp_so0l. Qed.

Lemma abortC c : <{[ abort ;; c ]}> =c <{[ c ;; abort ]}>.
Proof. by rewrite abortIx abortxI. Qed.

(* proposition 5.4 (2) : sequential composition, commutativity *)
Lemma seqcC c1 c2 {H : `{{cmd_disj c1 c2}}} :
  <{[ c1 ;; c2 ]}> =c <{[ c2 ;; c1 ]}>.
Proof.
move: H=>/cmd_disjP P1; rewrite eq_fsem.unlock !fsemE.
move: (fsem_local c1) (fsem_local c2)=>[U1 ->][U2 ->].
by rewrite liftfso_compC // disjoint_sym.
Qed.

(* proposition 5.4 (3) : sequential composition, associativity *)
Lemma seqcA c0 c1 c2 :
  <{[ c0 ;; c1 ;; c2 ]}> =c <{[ c0 ;; (c1 ;; c2) ]}>.
Proof. by rewrite eq_fsem.unlock !fsemE comp_soA. Qed.

(* proposition 5.4 (4) : sequentiality *)
Lemma if_seqc T (x : 'QReg[T]) (P : {hspace 'Ht T}) c0 c1 c2 c3 
  {H0 : `{{ cmd_var_disj x c0 }}} {H1 : `{{ cmd_var_disj x c1 }}} :
  let M := pmeas P in
  <{[ (c0 ◁ M[x] ▷ c1) ;; (c2 ◁ M[x] ▷ c3) ]}> =c 
    <{[ (c0 ;; c2) ◁ M[x] ▷ (c1 ;; c3) ]}>.
Proof.
move=>M. move: (fsem_local c0) (fsem_local c1) => [e0 P0] [e1 P1].
rewrite eq_fsem.unlock !fsemE P0 P1 -!liftfso_formso -!comp_soA.
rewrite ![liftfso _ :o liftfso (formso _)]liftfso_compC.
1,2: by rewrite disjoint_sym; apply/cmd_var_disjP.
rewrite comp_soDl !comp_soDr !comp_soA !comp_soACA -!liftfso_comp !formso_comp
  !tf2f_comp.
by rewrite /= /pmeas hsOx_comp hsxO_comp tf2f0 formso0 linear0 
  !(comp_so0r, comp_so0l) addr0 add0r !projf_idem.
Qed.

(* proposition 5.4 (5) : sequential composition, right-distributivity *)
Lemma seqc_distrl T (x : qreg T) M c0 c1 c :
  <{[ (c0 ◁ M[x] ▷ c1) ;; c ]}> =c <{[ (c0 ;; c) ◁ M[x] ▷ (c1 ;; c) ]}>.
Proof. by rewrite eq_fsem.unlock !fsemE comp_soDr !comp_soA. Qed.

(* proposition 5.4 (6) : sequential composition, left-distributivity-I *)
Lemma seqc_distrr T (x : qreg T) M c0 c1 c {H : `{{cmd_var_disj x c}}} :
  <{[ c ;; (c0 ◁ M[x] ▷ c1) ]}> =c <{[ (c ;; c0) ◁ M[x] ▷ (c ;; c1) ]}>.
Proof.
move: (fsem_local c)=>[y Py].
by rewrite eq_fsem.unlock !fsemE !Py comp_soDl -!comp_soA -!liftfso_formso
  ![_ :o liftfso y]liftfso_compC// cmd_var_disjP.
Qed.

(* proposition 5.4 (7) : sequential composition, left-distributivity-II *)
Lemma seqc_distrr2 T1 T2 (x1 : qreg T1) (x2 : qreg T2) (M : 'QM) (N : 'QM) c c0 c1 :
  <{[ c ;; '[ M[x1] ) ]}> =c <{[ '[ N[x2] ) ;; c ]}> ->
  <{[ c ;; '( M[x1] ] ]}> =c <{[ '( N[x2] ] ;; c ]}> -> 
  <{[ c ;; (c0 ◁ M[x1] ▷ c1) ]}> =c <{[ (c ;; c0) ◁ N[x2] ▷ (c ;; c1) ]}>.
Proof.
rewrite eq_fsem.unlock !fsemE !comp_so0l !add0r !addr0 !comp_so1l=>P1 P2.
by rewrite comp_soDl -!comp_soA; do 2 f_equal.
Qed.

Lemma seqc_distrUr T (x : 'QReg[T]) (M : 'QM) (U : 'FU) c0 c1 :
  let UM := measUr M U in
  <{[ ([cir [x] *= U ]) ;; (c0 ◁ M[x] ▷ c1) ]}> =c 
    <{[ c0 ◁ UM[x] ▷ c1 ]}>.
Proof.
rewrite /= eq_fsem.unlock !fsemE usemE comp_soDl -!comp_soA; do 2 f_equal;
by rewrite formso_comp -liftf_lf_comp tf2f_comp.
Qed.

(* Proposition 5.5 : qif - if interplay *)
Lemma qif_if T (F : finType) (x : 'QReg[T]) (phi : 'ONB(F; 'Ht T)) 
  (u : F -> ucmd_) (c : F -> cmd_) {H : `{{forall i, (ucmd_var_disj x (u i))}}}:
  <{[ [cir qif phi[x] = i then u i fiq] ;; If (onb_meas phi)[x] = i then c i fI]}> =c <{[ If (onb_meas phi)[x] = i then seqc_ (circuit_ (u i)) (c i) fI]}>.
Proof.
rewrite eq_fsem.unlock !fsemE !ifso_elem linear_suml/=.
apply eq_bigr=>i _; rewrite /elemso liftf_funE tm2mE onb_measE !fsemE 
  -!comp_soA !usemE !formso_comp; do 2 f_equal.
rewrite linear_sumr/= (bigD1 i)//= big1=>[j /negPf nji|];
rewrite !comp_lfunA -liftf_lf_comp tf2f_comp outp_comp onb_dot.
by rewrite eq_sym nji scale0r !linear0 !comp_lfun0l.
move: (usem_local (u i))=>[U ->].
rewrite eqxx scale1r addr0 [in LHS]liftf_lf_compC ?ucmd_var_disj_vsetP//.
by rewrite -comp_lfunA -liftf_lf_comp tf2f_comp outp_comp ns_dot scale1r.
Qed.

(* proposition 6.3 (1) : loop law, fixpoint  *)
Lemma while_fixpoint T (x : 'QReg[T]) M P :
  <{[ M[x] * P ]}> =c <{[ M[x] ▷ (P ;; (M[x] * P)) ]}>.
Proof.
by rewrite eq_fsem.unlock !fsemE {1}whileso_fixpoint/= 
  (ifso_bool true) !eqxx/= !liftf_funE/= /elemso tm2mE.
Qed.

(* proposition 6.3 (2) : loop law, unfolding *)
Lemma while_unfold T (x : 'QReg[T]) (M N : 'QM) P :
  M ∝ N -> <{[ N[x] ▷ (M[x] * P) ]}> =c <{[ N[x] ▷ (P ;; (M[x] * P)) ]}>.
Proof. by rewrite {1}while_fixpoint; apply: if_weaker. Qed.

(* proposition 6.3 (2) : loop law, elimination *)
Lemma while_elim T (x : 'QReg[T]) (M N : 'QM) P :
  M ^m⟂ ∝ N -> <{[ N[x] ▷ (M[x] * P) ]}> =c <{[ '[ N[x] ] ]}>.
Proof. by rewrite while_fixpoint; apply: if_weakerrl. Qed.

(* proposition 6.3 (3) : loop law, postcondition *)
Lemma while_post T (x : 'QReg[T]) (M N : 'QM) P :
  N ≫ M -> <{[ M[x] * P ]}> =c <{[ (M[x] * P) ;; ('[ N[x] ]) ]}>.
Proof.
move=>/meas_contradictP [] [c Pc P1] P2.
rewrite eq_fsem.unlock !fsemE whileso.unlock -so_comp_limr.
apply: whileso_is_cvg.
apply eq_lim=>n; rewrite whileso_iter_incrE comp_soA; f_equal.
rewrite !comp_so1l /elemso/= comp_soDl !formso_comp liftf_funE tm2mE
  -!liftf_lf_comp !tf2f_comp.
rewrite P2 tf2f0 linear0 formso0 addr0; apply/superopP=>y.
by rewrite P1 !linearZ/= !formsoE adjfZ 
  !(linearZl, linearZr)/= scalerA -normCKC Pc expr1n scale1r.
Qed.

End QWhileLaw.

Section QWhileNormalForm.


End QWhileNormalForm.

(*****************************************************************************)
(*                                 Automation                                *)
(*****************************************************************************)
(* solving cmd_expose *)
Module Export QWhileAuto.
Export CircuitAuto.

HB.lock Definition cmd_var_disj_lock := cmd_var_disj.
Lemma cmd_var_disj_lockE : cmd_var_disj = cmd_var_disj_lock.
Proof. by rewrite cmd_var_disj_lock.unlock. Qed.
HB.lock Definition cmd_disj_lock := cmd_disj.
Lemma cmd_disj_lockE : cmd_disj = cmd_disj_lock.
Proof. by rewrite cmd_disj_lock.unlock. Qed.
HB.lock Definition cmd_ucmd_disj_lock := cmd_ucmd_disj.
Lemma cmd_ucmd_disj_lockE : cmd_ucmd_disj = cmd_ucmd_disj_lock.
Proof. by rewrite cmd_ucmd_disj_lock.unlock. Qed.

Lemma cmd_var_disj_lock_skip T (x : qreg T) : cmd_var_disj_lock x skip_.
Proof. by rewrite -cmd_var_disj_lockE. Qed.

Lemma cmd_var_disj_lock_abort T (x : qreg T) : cmd_var_disj_lock x abort_.
Proof. by rewrite -cmd_var_disj_lockE. Qed.

Lemma cmd_var_disj_lock_init T1 T2 (x1 : qreg T1) (x2 : qreg T2) v : 
  disjoint_qreg x1 x2 -> cmd_var_disj_lock x1 (init_ x2 v).
Proof. by rewrite -cmd_var_disj_lockE. Qed.

Lemma cmd_var_disj_lock_circuit T (x : qreg T) u : 
  ucmd_var_disj_lock x u -> cmd_var_disj_lock x (circuit_ u).
Proof. by rewrite -cmd_var_disj_lockE -ucmd_var_disj_lockE. Qed.

Lemma cmd_var_disj_lock_cond2 T1 T2 (x1 : qreg T1) (x2 : qreg T2) M c0 c1 :
  disjoint_qreg x1 x2 -> cmd_var_disj_lock x1 c0 -> cmd_var_disj_lock x1 c1 ->
  cmd_var_disj_lock x1 (cond2_ x2 M c0 c1).
Proof. by rewrite -cmd_var_disj_lockE cond2_.unlock/==>->??; apply/forallP; case. Qed.

Lemma cmd_var_disj_lock_cond T1 T2 (F : finType) 
  (x1 : qreg T1) (x2 : qreg T2) M (f : F -> cmd_) :
  disjoint_qreg x1 x2 -> (forall i, cmd_var_disj_lock x1 (f i)) ->
  cmd_var_disj_lock x1 (cond_ x2 M f).
Proof. by rewrite -cmd_var_disj_lockE/==>->?; apply/forallP. Qed.

Lemma cmd_var_disj_lock_sequ T (x : qreg T) c1 c2 :
  cmd_var_disj_lock x c1 -> cmd_var_disj_lock x c2 ->
  cmd_var_disj_lock x (seqc_ c1 c2).
Proof. by rewrite -cmd_var_disj_lockE /==>->->. Qed.

Lemma cmd_var_disj_lock_while T1 T2 (x1 : qreg T1) (x2 : qreg T2) M c :
  disjoint_qreg x1 x2 -> cmd_var_disj_lock x1 c ->
  cmd_var_disj_lock x1 (while_ x2 M c).
Proof. by rewrite -cmd_var_disj_lockE /==>->->. Qed.

Lemma cmd_var_disj_lock_if T (x : qreg T) b u0 u1 :
  cmd_var_disj_lock x u0 -> cmd_var_disj_lock x u1 ->
    cmd_var_disj_lock x (if b then u0 else u1).
Proof. by case: b. Qed.

Ltac tac_cmd_var_disj := repeat match goal with
  | [ |- forall _ , _ ] => intros; 
          rewrite /= ?(eq_qreg_fst, eq_qreg_snd, eq_qreg_tuplei, eq_qreg_ffuni)/=
  | [ H : is_true (cmd_var_disj_lock ?x ?y) |- is_true (cmd_var_disj_lock ?x ?y) ] => 
          apply H
  | [ |- is_true (cmd_var_disj_lock _ abort_)] => 
          apply/cmd_var_disj_lock_abort
  | [ |- is_true (cmd_var_disj_lock _ skip_)] => 
          apply/cmd_var_disj_lock_skip
  | [ |- is_true (cmd_var_disj_lock _ (init_ _ _))] => 
          apply/cmd_var_disj_lock_init
  | [ |- is_true (cmd_var_disj_lock _ (circuit_ _))] => 
          apply/cmd_var_disj_lock_circuit
  | [ |- is_true (cmd_var_disj_lock _ (seqc_ _ _))] => 
          apply/cmd_var_disj_lock_sequ
  | [ |- is_true (cmd_var_disj_lock _ (cond2_ _ _ _ _))] => 
          apply/cmd_var_disj_lock_cond2
  | [ |- is_true (cmd_var_disj_lock _ (cond_ _ _ _))] => 
          apply/cmd_var_disj_lock_cond
  | [ |- is_true (cmd_var_disj_lock _ (while_ _ _ _))] => 
          apply/cmd_var_disj_lock_while
  | [ |- is_true (cmd_var_disj_lock _ (if _ then _ else _)) ] =>
          rewrite ?eqxx/=; try apply/cmd_var_disj_lock_if
  | [ |- is_true (disjoint_qreg _ _) ] => QRegAuto.tac_expose
  | [ |- is_true (ucmd_var_disj_lock _ _) ] => tac_ucmd_var_disj
end.

Lemma cmd_ucmd_disj_lock_uskip c : cmd_ucmd_disj_lock uskip_ c.
Proof. by rewrite -cmd_ucmd_disj_lockE. Qed.

Lemma cmd_ucmd_disj_lock_unitary T (x : qreg T) U c : 
  cmd_var_disj_lock x c -> cmd_ucmd_disj_lock (unitary_ x U) c.
Proof. by rewrite -cmd_ucmd_disj_lockE -cmd_var_disj_lockE. Qed.

Lemma cmd_ucmd_disj_lock_sequ u1 u2 c : 
  cmd_ucmd_disj_lock u1 c -> cmd_ucmd_disj_lock u2 c ->
    cmd_ucmd_disj_lock (sequ_ u1 u2) c.
Proof. by rewrite -cmd_ucmd_disj_lockE/==>->->. Qed.

Lemma cmd_ucmd_disj_lock_qcond2 (x : qreg Bool) phi u0 u1 c : 
  cmd_var_disj_lock x c -> cmd_ucmd_disj_lock u0 c -> cmd_ucmd_disj_lock u1 c ->
    cmd_ucmd_disj_lock (qcond2_ x phi u0 u1) c.
Proof.
rewrite -cmd_ucmd_disj_lockE/= qcond2_.unlock/= -cmd_var_disj_lockE=>->??; 
by apply/forallP; case.
Qed.

Lemma cmd_ucmd_disj_lock_qcond T (F : finType) (x : qreg T) phi (f : F -> ucmd_) c : 
  cmd_var_disj_lock x c -> (forall i, cmd_ucmd_disj_lock (f i) c) -> 
    cmd_ucmd_disj_lock (qcond_ x phi f) c.
Proof. by rewrite -cmd_ucmd_disj_lockE/= -cmd_var_disj_lockE=>->?; apply/forallP. Qed.

Lemma cmd_ucmd_disj_lock_if b u0 u1 c :
  cmd_ucmd_disj_lock u0 c -> cmd_ucmd_disj_lock u1 c ->
    cmd_ucmd_disj_lock (if b then u0 else u1) c.
Proof. by case: b. Qed.

Ltac tac_cmd_ucmd_disj := repeat match goal with
  | [ |- forall _ , _ ] => intros; 
          rewrite /= ?(eq_qreg_fst, eq_qreg_snd, eq_qreg_tuplei, eq_qreg_ffuni)/=
  | [ H : is_true (cmd_ucmd_disj_lock ?x ?y) |- is_true (cmd_ucmd_disj_lock ?x ?y) ] => 
          apply H
  | [ |- is_true (cmd_ucmd_disj_lock uskip_ _)] => 
          apply/cmd_ucmd_disj_lock_uskip
  | [ |- is_true (cmd_ucmd_disj_lock (unitary_ _ _) _)] => 
          apply/cmd_ucmd_disj_lock_unitary
  | [ |- is_true (cmd_ucmd_disj_lock (sequ_ _ _) _)] => 
          apply/cmd_ucmd_disj_lock_sequ
  | [ |- is_true (cmd_ucmd_disj_lock (qcond2_ _ _ _ _) _)] => 
          apply/cmd_ucmd_disj_lock_qcond2
  | [ |- is_true (cmd_ucmd_disj_lock (qcond_ _ _ _) _)] => 
          apply/cmd_ucmd_disj_lock_qcond
  | [ |- is_true (cmd_ucmd_disj_lock (if _ then _ else _) _) ] =>
          rewrite ?eqxx/=; try apply/cmd_ucmd_disj_lock_if
  | [ |- is_true (cmd_var_disj_lock _ _) ] => tac_cmd_var_disj
end.

Lemma cmd_disj_lock_abort c : cmd_disj_lock abort_ c.
Proof. by rewrite -cmd_disj_lockE. Qed.

Lemma cmd_disj_lock_skip c : cmd_disj_lock skip_ c.
Proof. by rewrite -cmd_disj_lockE. Qed.

Lemma cmd_disj_lock_init T (x : qreg T) v c : 
  cmd_var_disj_lock x c -> cmd_disj_lock (init_ x v) c.
Proof. by rewrite -cmd_disj_lockE/= -cmd_var_disj_lockE. Qed.

Lemma cmd_disj_lock_circuit u c : 
  cmd_ucmd_disj_lock u c -> cmd_disj_lock (circuit_ u) c.
Proof. by rewrite -cmd_disj_lockE -cmd_ucmd_disj_lockE. Qed.

Lemma cmd_disj_lock_cond2 T (x : qreg T) M c0 c1 c :
  cmd_var_disj_lock x c -> cmd_disj_lock c0 c -> cmd_disj_lock c1 c ->
    cmd_disj_lock (cond2_ x M c0 c1) c.
Proof. by rewrite -cmd_disj_lockE -cmd_var_disj_lockE cond2_.unlock/==>->??; apply/forallP; case. Qed.

Lemma cmd_disj_lock_cond T (F : finType) (x : qreg T) M (f : F -> cmd_) c :
  cmd_var_disj_lock x c -> (forall i, cmd_disj_lock (f i) c) ->
    cmd_disj_lock (cond_ x M f) c.
Proof. by rewrite -cmd_disj_lockE -cmd_var_disj_lockE/==>->?; apply/forallP. Qed.

Lemma cmd_disj_lock_sequ c1 c2 c :
  cmd_disj_lock c1 c -> cmd_disj_lock c2 c ->
  cmd_disj_lock (seqc_ c1 c2) c.
Proof. by rewrite -cmd_disj_lockE /==>->->. Qed.

Lemma cmd_disj_lock_while T (x : qreg T) M c1 c :
  cmd_var_disj_lock x c -> cmd_disj_lock c1 c ->
  cmd_disj_lock (while_ x M c1) c.
Proof. by rewrite -cmd_disj_lockE -cmd_var_disj_lockE/==>->->. Qed.

Lemma cmd_disj_lock_if b c0 c1 c :
  cmd_disj_lock c0 c -> cmd_disj_lock c1 c ->
    cmd_disj_lock (if b then c0 else c1) c.
Proof. by case: b. Qed.

Lemma cmd_disjC c1 c2 : cmd_disj c1 c2 = cmd_disj c2 c1.
Proof.
elim: c1 c2=>/=.
- elim=>//=[|?<-?<-//|????? IH].
  - by elim=>//=[?<-?<-//|????? IH]; symmetry; apply/forallP=>?. 
  - by symmetry; apply/forallP.
- elim=>//=[|?<-?<-//|????? IH].
  - by elim=>//=[?<-?<-//|????? IH]; symmetry; apply/forallP=>?. 
  - by symmetry; apply/forallP.
- move=>???; elim=>//=[???||?->?->//|????? IH|???? <-].
  - by rewrite QRegAuto.disjoint_qregC.
  - elim=>//=[???|?->?->//|????? IH];
    rewrite QRegAuto.disjoint_qregC//; f_equal;
    by under eq_forallb do rewrite IH.
  - rewrite QRegAuto.disjoint_qregC; f_equal;
    by under eq_forallb do rewrite IH.
  - by rewrite QRegAuto.disjoint_qregC.
- move=>u; elim=>//=.
  - by elim: u=>//=[?->?->//|????? IH]; apply/forallP.
  - by elim: u=>//=[?->?->//|????? IH]; apply/forallP.
  - move=>???; elim: u=>//=[???|?->?->//|????? IH]; 
    by rewrite QRegAuto.disjoint_qregC//; under eq_forallb do rewrite IH.
  - elim: u=>//=.
    - by elim=>//=[?->?->|????? IH]; rewrite ?andbb//; symmetry; apply/forallP.
    - move=>???; elim=>//=[???|?<-?<-//|????? IH];
      by rewrite QRegAuto.disjoint_qregC//; under eq_forallb do rewrite IH.
    - move=>?+?+u; move=>->->; elim: u=>//=[?<-?<-|????? IH];
      by rewrite andbACA// forallb_and; under eq_forallb do rewrite IH.
    - move=>????? IH; elim=>//=.
      - by apply/forallP=>?; rewrite IH.
      - by move=>???; rewrite QRegAuto.disjoint_qregC; under eq_forallb do rewrite IH.
      - by move=>?<-?<-; rewrite andbACA forallb_and; under eq_forallb do rewrite IH/= -!IH.
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
  - move=>?<-?<-; elim: u=>//=[?->?->|????? IH];
    by rewrite andbACA// forallb_and; under eq_forallb do rewrite IH.
  - move=>????? IH; under eq_forallb do rewrite -IH; clear.
    elim: u=>//=.
    - by symmetry; apply/forallP.
    - by move=>???; rewrite QRegAuto.disjoint_qregC.
    - by move=>?->?->; rewrite andbACA forallb_and.
    - move=>????? IH; rewrite QRegAuto.disjoint_qregC -!andbA; f_equal.
      apply/eqb_iff; split.
        move=>/andP[]/forallP P1 /forallP P2; apply/andP; split; apply/forallP=>i.
        by move: (P2 i); rewrite IH/==>/andP[].
        rewrite P1/=; apply/forallP=>j.
        by move: (P2 j); rewrite !IH/==>/andP[] _ /forallP.
      move=>/andP[]/forallP P1 /forallP P2; apply/andP; split; apply/forallP=>i.
      by move: (P2 i)=>/andP[].
      rewrite IH/=; apply/andP; split=>//; apply/forallP=>j.
      by move: (P2 j)=>/andP[] _ /forallP.
  - move=>????<-; elim: u=>//=.
    - by move=>???; rewrite QRegAuto.disjoint_qregC.
    - by move=>?->?->; rewrite andbACA.
    - by move=>????? IH; rewrite andbACA QRegAuto.disjoint_qregC forallb_and;
      under eq_forallb do rewrite IH.
- move=>? IH1? IH2 c2; rewrite IH1 IH2; elim: c2=>//=.
  - elim=>//=[?<-?<-|????? IH];
    by rewrite andbACA// forallb_and; under eq_forallb do rewrite IH.
  - by move=>?<-?<-; rewrite !andbA; f_equal; rewrite -!andbA; f_equal; rewrite andbC.
  - by move=>????? IH; rewrite andbACA forallb_and; under eq_forallb do rewrite IH.
  - by move=>???? IH; rewrite andbACA IH.
- move=>????? IH; elim=>//=.
  - by apply/forallP=>?; rewrite IH.
  - by apply/forallP=>?; rewrite IH.
  - by move=>???; rewrite QRegAuto.disjoint_qregC; under eq_forallb do rewrite IH.
  - elim=>//=.
    - by apply/forallP=>?; rewrite IH.
    - by move=>???; rewrite QRegAuto.disjoint_qregC; under eq_forallb do rewrite IH.
    - move=>?<-?<-; rewrite andbACA forallb_and; under eq_forallb do rewrite IH/=;
      by under [in RHS]eq_forallb do rewrite !IH.
    - move=>????? IH1; rewrite QRegAuto.disjoint_qregC -!andbA; f_equal.
      apply/eqb_iff; split.
        move=>/andP[]/forallP P1 /forallP P2; apply/andP; split; apply/forallP=>i.
        by move: (P2 i); rewrite IH/==>/andP[].
        rewrite -IH1; apply/andP; split=>//; apply/forallP=>j.
        by move: (P2 j); rewrite !IH/==>/andP[] _ /forallP.
      move=>/andP[]/forallP P1 /forallP P2; apply/andP; split; apply/forallP=>i.
      by move: (P2 i); rewrite -IH1/==>/andP[].
      rewrite IH/=; apply/andP; split=>//; apply/forallP=>j.
      by move: (P2 j); rewrite -IH1/==>/andP[] _ /forallP/(_ i); rewrite IH.
  - move=>?<-?<-; rewrite andbACA forallb_and; f_equal.
    by under eq_forallb do rewrite IH/= -!IH.
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
  - move=>????<-; rewrite andbACA QRegAuto.disjoint_qregC forallb_and; f_equal.
    by under eq_forallb do rewrite IH/= -IH.
- move=>???? IH; elim=>//=.
  - by move=>???; rewrite QRegAuto.disjoint_qregC IH.
  - elim=>//=.
    - by move=>???; rewrite QRegAuto.disjoint_qregC IH.
    - by move=>?<-?<-; rewrite andbACA !IH.
    - move=>????? IH1; rewrite QRegAuto.disjoint_qregC IH/= andbACA forallb_and;
      by under [in RHS]eq_forallb do rewrite -IH1 IH.
  - by move=>?<-?<-; rewrite andbACA; f_equal; rewrite !IH/=.
  - move=>????? IH1; rewrite IH/= andbACA QRegAuto.disjoint_qregC; f_equal.
    by rewrite forallb_and; under eq_forallb do rewrite -IH IH1.
  - by move=>????<-; rewrite !IH/= andbACA QRegAuto.disjoint_qregC.
Qed.

Lemma cmd_disj_lockC c1 c2 : cmd_disj_lock c1 c2 = cmd_disj_lock c2 c1.
Proof. by rewrite -cmd_disj_lockE cmd_disjC. Qed.

Ltac tac_cmd_disj := repeat match goal with
  | [ |- forall _ , _ ] => intros; 
          rewrite /= ?(eq_qreg_fst, eq_qreg_snd, eq_qreg_tuplei, eq_qreg_ffuni)/=
  | [ H : is_true (cmd_disj_lock ?x ?y) |- is_true (cmd_disj_lock ?x ?y)] => 
          apply H
  | [ H : is_true (cmd_disj_lock ?x ?y) |- is_true (cmd_disj_lock ?y ?x)] => 
          rewrite cmd_disj_lockC; apply H
  | [ |- is_true (cmd_disj_lock abort_ _)] => 
          apply/cmd_disj_lock_abort
  | [ |- is_true (cmd_disj_lock skip_ _)] => 
          apply/cmd_disj_lock_skip
  | [ |- is_true (cmd_disj_lock (init_ _ _) _)] => 
          apply/cmd_disj_lock_init
  | [ |- is_true (cmd_disj_lock (circuit_ _) _)] => 
          apply/cmd_disj_lock_circuit
  | [ |- is_true (cmd_disj_lock (seqc_ _ _) _)] => 
          apply/cmd_disj_lock_sequ
  | [ |- is_true (cmd_disj_lock (cond2_ _ _ _ _) _)] => 
          apply/cmd_disj_lock_cond2
  | [ |- is_true (cmd_disj_lock (cond_ _ _ _) _)] => 
          apply/cmd_disj_lock_cond
  | [ |- is_true (cmd_disj_lock (while_ _ _ _) _)] => 
          apply/cmd_disj_lock_while
  | [ |- is_true (cmd_disj_lock (if _ then _ else _) _) ] =>
          rewrite ?eqxx/=; try apply/cmd_disj_lock_if
  | [ |- is_true (cmd_var_disj_lock _ _) ] => tac_cmd_var_disj
  | [ |- is_true (cmd_ucmd_disj_lock _ _) ] => tac_cmd_ucmd_disj
end.

Ltac tac_qwhile_auto := rewrite /cmd_expose ?ucmd_var_disj_lockE
  ?ucmd_disj_lockE ?ucmd_var_subset_lockE ?ucmd_wf_lockE
  ?cmd_var_disj_lockE ?cmd_disj_lockE ?cmd_ucmd_disj_lockE;
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
  | [ |- is_true (cmd_var_disj_lock _ _)] => tac_cmd_var_disj
  | [ |- is_true (cmd_disj_lock _ _)] => tac_cmd_disj
  | [ |- is_true (cmd_ucmd_disj_lock _ _)] => tac_cmd_ucmd_disj
  end.

Module Exports.
Global Hint Extern 0 (cmd_expose _) => (tac_qwhile_auto) : typeclass_instances.

(*
Goal forall T (x : 'QReg[T]) U, `{{ucmd_wf (unitary_ x U)}}.
Proof. intros. tac_qwhile_auto. Qed.

Goal forall T (x : 'QReg[T]) U, `{{ucmd_var_subset x (unitary_ x U)}}.
Proof. intros. tac_qwhile_auto. Qed.

Goal forall T1 T2 (x : 'QReg[T1 * T2]) U1 U2,
  `{{ucmd_disj (unitary_ <{x.1}> U1) (unitary_ <{x.2}> U2)}}.
Proof. intros. tac_qwhile_auto. Qed.

Goal forall T1 T2 (x : 'QReg[T1 * T2]) U2,
  `{{ucmd_wf (qcond_ <{x.1}> t2tv (fun i => unitary_ <{x.2}> U2))}}.
Proof. intros. tac_qwhile_auto. Qed.

Goal forall T (x : 'QReg[Bool * T]) U2,
  `{{ucmd_wf (qcond2_ <{x.1}> t2tv uskip_ (unitary_ <{x.2}> U2))}}.
Proof. intros. tac_qwhile_auto. Qed.

Goal forall T1 T2 (x : 'QReg[T1 * T2]) U1 U2,
  <{[ [x.1] *= U1 ; [x.2] *= U2 ]}> =u <{[ [x.2] *= U2 ; [x.1] *= U1 ]}>.
Proof. by intros; rewrite sequC. Qed.

Goal forall T1 T2 (x : 'QReg[T1 * T2]) U1 U2,
  <{[ [cir [x.1] *= U1] ;; [cir [x.2] *= U2] ]}> =c <{[ [cir [x.2] *= U2 ; [x.1] *= U1] ]}>.
Proof. by intros; rewrite sequC -seqc_circuit. Qed.

Goal forall T1 T2 (x : 'QReg[T1 * T2]) U1 U2,
  <{[ [cir [x.1] *= U1] ;; [cir [x.2] *= U2] ]}> =c <{[ [cir [x.2] *= U2 ; [x.1] *= U1] ]}>.
Proof. by intros; rewrite seqcC seqc_circuit. Qed.
*)
End Exports.
End QWhileAuto.

Section Example.
Import QWhileAuto.Exports.

Variable (q : 'QReg[Bool * (Bool * Bool)]).

Let c_skip :=
<{[  [q.2.1] := '0 ;; 
     [q.2.2] := '0 ;; 
     [cir [q.1] → ([q.2.1] *= ''X)] ;;
     [cir [q.1] → ([q.2.2] *= ''X)] ;;
     [cir [q.1] → ([q.2.2] *= ''X)] ;;
     [cir [q.1] → ([q.2.1] *= ''X)] ;;
     [ q.2.2 ] ▷ ([ q.2.1 ] ▷ [cir [q.1] *= ''X])
     ]}>.

Goal c_skip =c <{[ [q.2.1] := '0 ;; [q.2.2] := '0 ]}>.
Proof.
rewrite /c_skip -!seqc_circuitA 2!qif_sequB -!sequA unit_sequ/=.
rewrite [in X in qcond2_ _ _ _ (sequ_ X _)]uskip_eqP/= ?PauliX_id//.
rewrite qif_sequB !uskipIx unit_sequ/= uskip_eqP/= ?PauliX_id//.
rewrite qif_idemB uskip_skip skipxI !seqcA init_ifFK/= ?onb_dot//=.
by rewrite skipxI.
Qed.

Let c_Xq :=
<{[  [q.2.1] := '0 ;; 
     [q.2.2] := '0 ;; 
     [cir [q.1] → ([q.2.1] *= ''X)] ;;
     [cir [q.1] → ([q.2.2] *= ''X)] ;;
     [cir [q.1] *= ''X] ;;
     [cir [q.1] → ([q.2.2] *= ''X)] ;;
     [cir [q.1] → ([q.2.1] *= ''X)] ;;
     [ q.2.2 ] ▷ ([ q.2.1 ] ▷ [cir [q.1] *= ''X])
     ]}>.

Goal c_Xq =c <{[ [q.2.1] := '1 ;; [q.2.2] := '1 ]}>.
Proof.
rewrite /c_Xq -!seqc_circuitA qif_sequB -!sequA qif_sequB -qchoice_sym.
rewrite sequA qif_sequB -!sequA !uskipIx !uskipxI sequC qif_idemB.
rewrite sequC sequA seqc_circuitA seqcA [in X in seqc_ X _]seqcA 
  (init_unitaryKP _ (v := '1 : 'NS('Ht Bool)))/= ?PauliX_cb//=.
rewrite seqcA -[in X in seqc_ _ X]seqcA [in X in seqc_ _ (seqc_ X _)]seqcC.
rewrite seqcA init_ifTK/= -!seqcA seqc_circuitA .
rewrite (init_unitaryKP _ (v := '1 : 'NS('Ht Bool)))/= ?PauliX_cb//=.
rewrite [in X in seqc_ X _]seqcA seqcC seqcA init_ifTK/= seqcC.
rewrite seqcA -[in X in seqc_ _ X]seqcA [in X in seqc_ _ X]seqcC -seqc_circuitA.
by rewrite unit_sequ/= uskip_eqP/= ?PauliX_id// uskip_skip skipxI seqcC.
Qed.

Let c_Xq1 :=
<{[  [q.2.1] := '0 ;; 
     [q.2.2] := '0 ;; 
     [cir [q.1] → ([q.2.1] *= ''X)] ;;
     [cir [q.1] → ([q.2.2] *= ''X)] ;;
     [cir [q.2.1] *= ''X] ;;
     [cir [q.1] → ([q.2.2] *= ''X)] ;;
     [cir [q.1] → ([q.2.1] *= ''X)] ;;
     [ q.2.2 ] ▷ ([ q.2.1 ] ▷ [cir [q.1] *= ''X])
     ]}>.

Goal c_Xq1 =c <{[ [q.2.1] := '1 ;; [q.2.2] := '0 ]}>.
Proof.
rewrite /c_Xq1 -{2}(@qif_idemB <{q.1}> t2tv <{[[q.2.1] *= ''X]}>).
rewrite -!seqc_circuitA !qif_sequB !uskipxI !uskipIx sequC.
rewrite -[X in sequ_ _ (sequ_ _ X)]sequA [in X in sequ_ _ (sequ_ _ X)]unit_sequ/=.
rewrite [in X in sequ_ _ (sequ_ _ X)]uskip_eqP/= ?PauliX_id// uskipIx.
rewrite [in X in sequ_ _ X]unit_sequ/= [in X in sequ_ _ X]uskip_eqP/= ?PauliX_id// uskipxI.
rewrite qif_idemB seqcC [X in seqc_ X _]seqcA.
rewrite (init_unitaryKP _ (v := '1 : 'NS('Ht Bool)))/= ?PauliX_cb//=.
by rewrite seqcC seqcA init_ifFK/= ?onb_dot// skipxI.
Qed.

Let c_Xq2 :=
<{[  [q.2.1] := '0 ;; 
     [q.2.2] := '0 ;; 
     [cir [q.1] → ([q.2.1] *= ''X)] ;;
     [cir [q.1] → ([q.2.2] *= ''X)] ;;
     [cir [q.2.2] *= ''X] ;;
     [cir [q.1] → ([q.2.2] *= ''X)] ;;
     [cir [q.1] → ([q.2.1] *= ''X)] ;;
     [ q.2.2 ] ▷ ([ q.2.1 ] ▷ [cir [q.1] *= ''X])
     ]}>.

Goal c_Xq2 =c <{[ [q.2.1] := '0 ;; [q.2.2] := '1 ]}>.
Proof.
rewrite /c_Xq2 -{2}(@qif_idemB <{q.1}> t2tv <{[[q.2.2] *= ''X]}>).
rewrite -!seqc_circuitA !qif_sequB !uskipxI !uskipIx sequC.
rewrite -[X in sequ_ _ X]sequA unit_sequ/=.
rewrite [in X in sequ_ _ (sequ_ X _)]uskip_eqP/= ?PauliX_id// uskipIx.
rewrite -sequA unit_sequ/= [in X in (sequ_ X _)]uskip_eqP/= ?PauliX_id// uskipIx.
rewrite qif_idemB [X in seqc_ X _]seqcA.
rewrite (init_unitaryKP _ (v := '1 : 'NS('Ht Bool)))/= ?PauliX_cb//=.
by rewrite seqcA init_ifTK/= -seqcA seqcC seqcA init_ifFK ?onb_dot// skipxI seqcC.
Qed.

End Example.

