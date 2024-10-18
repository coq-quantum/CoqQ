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

(****************************************************************************)
(*            Semantics and QLaws for Recursive Quantum Program             *)
(****************************************************************************)

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
(*                     recurive without nondeterministic                     *)
(*****************************************************************************)

(* F is the finite set of identifier *)
Inductive cmd_ {F : finType} : Type :=
    | skip_ 
    | abort_
    | init_      T of qreg T & 'NS('Ht T)
    | circuit_   of ucmd_
    | seqc_      of cmd_ & cmd_
    | cond_      T (f: finType) (x : qreg T) of 'QM(f;'Ht T) & (f -> cmd_)
    | while_     T (x : qreg T) of 'QM(bool;'Ht T) & cmd_
    | call_      of F.

Definition proc_ (F : finType) := F -> @cmd_ F.

Fixpoint no_call_ {F : finType} (c : @cmd_ F) : bool :=
  match c with
  | skip_ => true
  | abort_ => true 
  | init_  _ _ _ => true 
  | circuit_ _ => true 
  | seqc_ c1 c2 => (no_call_ c1) && (no_call_ c2)
  | cond_  _ _ _ _ c => [forall i, (no_call_ (c i))]
  | while_ _ _ _ c => no_call_ c
  | call_ _ => false
  end.

HB.lock
Definition cond2_ (F : finType) T (x : qreg T) (M : 'QM(bool; 'Ht T)) (c0 c1 : @cmd_ F) :=
  @cond_ F T bool x M (fun b => if b then c1 else c0).

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
Notation "'call' i" := (call_ i) (in custom cmd at level 20, i constr,
  format "'call'  i").

Notation b0 := (choi2so (dim 'H[msys]_finset.setT)%:R%:M).
Notation setT := finset.setT.
Notation set0 := finset.set0.

Module Export Semantics.
From mathcomp.analysis Require Import topology.
From mathcomp.classical Require Import functions.
Import QOCPO.Exports.
Local Open Scope classical_set_scope.

Section semantics1.
Variable (F : finType) (f : proc_ F).
Local Notation cmd_ := (@cmd_ F).

(* to evaluate the semantics, we should give the concrete definition 
   of proc identifier, i.e., given fun i : F => cmd_ *)

(* syntactical replacement, we replace each proc (call i) to (X i) *)
Fixpoint rep (c : cmd_) (X : F -> cmd_) : cmd_ :=
  match c with
  | skip_ => skip_
  | abort_ => abort_
  | init_ T x v => init_ x v
  | circuit_  u => circuit_ u
  | seqc_ c1 c2 => seqc_ (rep c1 X) (rep c2 X)
  | cond_  T f x M fc => cond_ x M (fun i => rep (fc i) X)
  | while_  T x M c => while_ x M (rep c X)
  | call_ i => X i
  end.

(* generalization of F^n(c) for any program c *)
Fixpoint repn (c : cmd_) n : cmd_ :=
  match n with
  | 0 => rep c (fun => abort_)
  | S n => rep c (fun i => repn (f i) n)
  end.

(* if program contains no function call, then its semantics is similar
   to qwhile program, i.e., we set call_ i to 0 *)
Fixpoint fsem_no_call (c : cmd_) : 'SO :=
  match c with
  | skip_ => \:1
  | abort_ => 0
  | init_ T x v => liftfso (initialso (tv2v x v))
  | circuit_  u => formso (usem u)
  | seqc_ c1 c2 => (fsem_no_call c2) :o (fsem_no_call c1)
  | cond_  T fT x M fc => 
      ifso (liftf_fun (tm2m x x M)) (fun i => fsem_no_call (fc i))
  | while_  T x M c => whileso (liftf_fun (tm2m x x M)) true (fsem_no_call c)
  | call_ i => 0
  end.

Lemma repn_seqcE c1 c2 i :
  repn (seqc_ c1 c2) i = seqc_ (repn c1 i) (repn c2 i).
Proof. by case: i. Qed.

Lemma repn_condE T G (x : qreg T) (M : 'QM(G;'Ht T)) (g : G -> cmd_) i :
  repn (cond_ x M g) i = cond_ x M (fun j => repn (g j) i).
Proof. by case: i. Qed.

Lemma repn_whileE T (x : qreg T) (M : 'QM) c i :
  repn (while_ x M c) i = while_ x M (repn c i).
Proof. by case: i. Qed.

Definition repnE := (repn_seqcE, repn_condE, repn_whileE).

(* if fi call-free, then use it to replace calls yields call-free program *)
Lemma rep_no_call c (fi : F -> cmd_) : 
  (forall i, no_call_ (fi i)) -> no_call_ (rep c fi).
Proof. by move=>Pi; elim: c=>//=[?->?->//|?????/forallP]. Qed.

(* F^n(c) contains no calls *)
Lemma repn_no_call c i : no_call_ (repn c i).
Proof.
elim: i c=>//=[c|n IH c].
by apply/rep_no_call.
by apply/rep_no_call=>i.
Qed.

End semantics1.

(* The semantics of c is the the limit of F^n(c)  *)
(*   recall that F^n(c) contains no calls, so its *)
(*   semantics is evaluated by fsem_no_call       *)
HB.lock
Definition fsem {F : finType} (f : proc_ F) (c : @cmd_ F) :=
  limn (fun n => fsem_no_call (repn f c n)).

Section semantics2.
Variable (F : finType) (f : proc_ F).
Local Notation cmd_ := (@cmd_ F).
Local Notation rep := (@rep F).
Local Notation repn := (@repn F f).
Local Notation fsem_no_call := (@fsem_no_call F).
Local Notation fsem := (@fsem F f).

(* semantics replacement, replace the semantics of (call i) to (X i) *)
Fixpoint reps (c : cmd_) (X : F -> 'SO) : 'SO :=
  match c with
  | skip_ => \:1
  | abort_ => 0
  | init_ T x v => liftfso (initialso (tv2v x v))
  | circuit_  u => formso (usem u)
  | seqc_ c1 c2 => (reps c2 X) :o (reps c1 X)
  | cond_  T fT x M fc => 
      ifso (liftf_fun (tm2m x x M)) (fun i => reps (fc i) X)
  | while_  T x M c => whileso (liftf_fun (tm2m x x M)) true (reps c X)
  | call_ i => X i
  end.

(* n-th iteration of semantics replacement *)
Fixpoint repsn (c : cmd_) n : 'SO :=
  match n with
  | 0 => reps c (fun=>0)
  | S n => reps c (fun i => repsn (f i) n)
  end.

(* equivalence between n-th iteration of 
  syntactical replacement and semantics replacement *)
Lemma repn_repsnE c n :
  fsem_no_call (repn c n) = repsn c n.
Proof.
elim: n c=>[|n IH];
by elim=>//=[?->?->|??????|????->]//; f_equal; apply/funext.
Qed.

Lemma fsem_repsnE c : fsem c = limn (fun n => repsn c n).
Proof. by rewrite fsem.unlock; apply eq_lim=>i; rewrite repn_repsnE. Qed.

Lemma reps_qo (c : cmd_) (X : F -> 'QO) : reps c X \is cptn.
Proof.
elim: c=>/=; intros. 1-3: apply: is_cptn.
by rewrite -krausso_qoP /trace_nincr big_ord1 bound1f_form_le1.
by rewrite (QOperation_BuildE H0) [X in _ :o X](QOperation_BuildE H) is_cptn.
under eq_fun do rewrite (QOperation_BuildE (H _)). apply: is_cptn.
by rewrite (QOperation_BuildE H); apply: is_cptn.
by apply: is_cptn.
Qed.
HB.instance Definition _ c (X : F -> 'QO) := isQOperation.Build _ _ _ (@reps_qo c X).

Lemma reps_leso c (X1 X2 : F -> 'QO) : 
  (forall i, (X1 i : 'SO) <= X2 i) -> 
    reps c X1 <= reps c X2.
Proof.
move=>IH.
elim: c.
1-4: intros; by rewrite lexx.
- move=>c1 IH1 c2 IH2 /=.
  apply: leso_comp2=>[||//|//]. 1,2: apply: cp_geso0.
- move=>T fT x M c Pi.
  rewrite /= !ifso_elem lev_sum=>[i _|//].
  by apply: leso_comp2r; [apply: Pi| rewrite cp_geso0].
- move=>T x M c Pc.
  by rewrite /= whileso_leso.
- by move=>i /=.
Qed.

Lemma repsnE (c : cmd_) n :
  repsn c n.+1 = reps c (fun i => repsn (f i) n).
Proof. by []. Qed.

Lemma repsn_qo (c : cmd_) n : repsn c n \is cptn.
Proof.
elim: n c=>[c/=|n IH c/=]; first by rewrite is_cptn.
under eq_fun do rewrite (QOperation_BuildE (IH _)).
by rewrite is_cptn.
Qed.
HB.instance Definition _ c n := isQOperation.Build _ _ _ (@repsn_qo c n).

Lemma repsn_homo c : nondecreasing_seq (repsn c).
Proof.
apply/cpo.chain_homo=>n.
elim: n c=>[c/=|n IH c].
by apply/reps_leso=>/=i; rewrite cp_geso0.
by rewrite repsnE repsnE; apply/reps_leso=>i; apply/IH.
Qed.

Lemma repsn_is_cvgn c : cvgn (repsn c).
Proof.
apply: (vnondecreasing_is_cvgn (b := b0) (repsn_homo c)).
move=>n; apply: qo_ubound.
Qed.

(* the semantics of recursive qwhile program is a cptn map, 
  i.e., is a quantum operation *)
Lemma fsem_qo c : fsem c \is cptn.
Proof.
rewrite fsem_repsnE.
suff : [set x : 'SO | x \is cptn]%classic (limn (repsn c)) by [].
apply: (@closed_cvg _ _ _ eventually_filter (repsn c) _ _ _ _)=>//.
apply closed_isqo. by apply: nearW=>x/=; apply is_cptn.
apply: repsn_is_cvgn.
Qed.
HB.instance Definition _ c := isQOperation.Build _ _ _ (fsem_qo c).

(* Proposition 3.1 , Structure represantation of fsem  *)
Lemma fsem_abortE : fsem <{[ abort ]}> = 0.
Proof.
rewrite fsem_repsnE; apply: norm_cvg_lim.
rewrite -cvg_shiftS/=; apply: cvg_cst.
Qed.

Lemma fsem_skipE : fsem <{[ skip ]}> = \:1.
Proof.
rewrite fsem_repsnE; apply: norm_cvg_lim.
rewrite -cvg_shiftS/=; apply: cvg_cst.
Qed.

Lemma fsem_initE T (x : qreg T) v : 
  fsem <{[ [x] := v ]}> = liftfso (initialso (tv2v x v)).
Proof.
rewrite fsem_repsnE; apply: norm_cvg_lim.
rewrite -cvg_shiftS/=; apply: cvg_cst.
Qed.

Lemma fsem_circuitE u : fsem <{[ [cir u ] ]}> = formso (usem u).
Proof.
rewrite fsem_repsnE; apply: norm_cvg_lim.
rewrite -cvg_shiftS/=; apply: cvg_cst.
Qed.

Lemma fsem_condE T (G : finType) (x : qreg T) M (fc : G -> cmd_) : 
  fsem <{[ If M[x] = i then fc i fI ]}> = 
    ifso (liftf_fun (tm2m x x M)) (fun i : G => fsem (fc i)).
Proof.
rewrite fsem_repsnE/= ifso_elem /=.
transitivity (\sum_i limn (fun n => repsn (fc i) n :o elemso (liftf_fun (tm2m x x M)) i)).
rewrite -lim_sum. move=>i _; apply: so_comp_is_cvgl. apply: repsn_is_cvgn.
apply eq_lim=>i; case: i=>[|i]/=;
by rewrite functions.fct_sumE ifso_elem; apply eq_bigr=>? _.
apply eq_bigr=>i _; rewrite so_comp_liml// ?fsem_repsnE//; apply: repsn_is_cvgn.
Qed.

Lemma fsem_cond2E T (x : qreg T) M c0 c1 : 
  fsem <{[ c0 ◁ M[x] ▷ c1 ]}> = 
    fsem c1 :o formso (liftf_lf (tf2f x x (M true))) + 
      (fsem c0 :o formso (liftf_lf (tf2f x x (M false)))).
Proof. by rewrite cond2_.unlock fsem_condE (ifso_bool true)/=. Qed.

(* the fixpoint characterization is given by whileso *)
Lemma fsem_whileE T (x : qreg T) M c : 
  fsem <{[ M[x] * c ]}> = whileso (liftf_fun (tm2m x x M)) true (fsem c).
Proof.
rewrite !fsem_repsnE -limn_shiftS/= whileso.unlock.
have P1 i : nondecreasing_seq (fun i0 : nat => whileso_iter (liftf_fun (tm2m x x M)) true (repsn c i0.+1) i).
  by apply/cpo.chain_homo=>j; apply/whileso_iter_leso/repsn_homo.
have P2 i : cvgn (fun i0 : nat => whileso_iter (liftf_fun (tm2m x x M)) true (repsn c i0.+1) i).
  apply: (vnondecreasing_is_cvgn (b := b0) (P1 i))=>j.
  apply/qo_ubound.
rewrite (exchange_limn_nondecreasing (b := b0) _ P1).
move=>i; apply/whileso_iter_homo.
move=>i j; apply/qo_ubound.
apply: eq_lim=> i; rewrite whileso_iter_limn=>[|//].
rewrite is_cvgn_shiftS; apply: repsn_is_cvgn.
by f_equal; rewrite limn_shiftS.
Qed.

Lemma fsem_callE i : fsem <{[ call i ]}> = fsem (f i).
Proof. by rewrite !fsem_repsnE/= -limn_shiftS/=. Qed.

Lemma fsem_seqE c1 c2 : fsem <{[ c1 ;; c2 ]}> = fsem c2 :o fsem c1.
Proof.
rewrite !fsem_repsnE/= -limn_shiftS/= so_comp_lim.
by move: (@repsn_is_cvgn c2); rewrite -is_cvgn_shiftS.
by move: (@repsn_is_cvgn c1); rewrite -is_cvgn_shiftS.
by f_equal; rewrite -[RHS]limn_shiftS.
Qed.

Definition fsemE := (fsem_abortE, fsem_skipE, fsem_initE, 
  fsem_circuitE, fsem_cond2E, fsem_condE, fsem_seqE, fsem_whileE, fsem_callE).

(* fixpoint : semantically replace the call by itself won't change the semantics *)
Lemma fsem_fixpoint c : 
  reps c (fun i => fsem (f i)) = fsem c.
Proof.
elim: c=>//=; intros; rewrite fsemE//.
by rewrite H H0.
by f_equal; apply/funext=>i.
by f_equal.
Qed.

(* equivalence between syntactic and semantic replacement *)
Lemma rep_reps (c : cmd_) (X : F -> cmd_) :
  fsem (rep c X) = reps c (fun i => fsem (X i)).
Proof.
elim: c.
1,2,3,4: intros; by rewrite /= fsemE.
by move=>c1 IH1 c2 IH2; rewrite /= fsemE IH1 IH2.
by move=>T fT x M c IH; rewrite /= fsemE; under eq_fun do rewrite IH.
by move=>T x M c IH; rewrite /= fsemE IH.
by move=>i.
Qed.

(* fixpoint : syntactically replace the call by itself won't change the semantics *)
Lemma fsem_rep_fxp c : fsem (rep c f) = fsem c.
Proof.
elim: c. 1-4: by [].
by move=>c1 IH1 c2 IH2; rewrite !fsemE -/rep -IH1 -IH2.
move=>T fT x M c Pi; rewrite !fsemE -/rep.
f_equal. by apply/funext.
by move=>T x M c IH; rewrite !fsemE -/rep IH.
by move=>j; rewrite /= fsemE.
Qed.

(* F(X) defined in Section 6 *)
Definition fX (X : F -> cmd_) := (fun i => rep (f i) X).

(* Proposition 6.2 (1) *)
Lemma fsem_fX_fxp i : fsem (fX f i) = fsem (f i).
Proof. exact: fsem_rep_fxp. Qed.

Definition fXs (X : F -> 'SO) := fun i => reps (f i) X.
HB.instance Definition _ (X : F -> 'QO) i := QOperation.on (fXs X i).

(* pointwise partial order *)
Definition fQO := F -> 'QO[msys]_setT.
HB.instance Definition _ := Order.POrder.on fQO.

Definition qo_fXs (X : fQO) : fQO := fXs X.

Lemma fXs_leso (X1 X2 : fQO) i : 
  (X1 <= X2)%O -> fXs X1 i <= fXs X2 i.
Proof. move=>/lefP; exact: reps_leso. Qed.

Lemma reps_cvgn c (g : nat -> fQO) (gn : F -> 'SO) :
  (nondecreasing_seq g) ->
  (forall i, (g ^~ i : nat -> 'SO) @ \oo --> gn i) -> 
    (fun i => reps c (g i)) @ \oo --> reps c gn.
Proof.
move=>gh Pg. elim: c.
1-4: intros=>/=; apply: cvg_cst.
- move=>c1 IH1 c2 IH2.
  rewrite /=; apply: so_comp_cvg. apply: IH2. apply: IH1.
- move=>T fT x M c IH; rewrite /= ifso_elem.
  have ->: (fun i => ifso (liftf_fun (tm2m x x M)) (fun i0 : fT => reps (c i0) (g i)))
    = (fun i => (\sum_j (fun i => (reps (c j) (g i) :o elemso (liftf_fun (tm2m x x M)) j))) i).
  by apply/funext=>i; rewrite fct_sumE ifso_elem.
  apply: cvg_sum=>i _. apply: so_comp_cvgl. apply: IH.
- move=>T x M c IH. rewrite /= vcvgn_limnE; split; last first.
    apply: (vnondecreasing_is_cvgn (b := b0)).
      by move=>n m /gh /lefP Pnm; apply: whileso_leso=>/=; apply: reps_leso=>i; apply: Pnm.
      move=>i; apply: qo_ubound.
  rewrite whileso.unlock (exchange_limn_nondecreasing (b := b0)).
    by move=>i; apply: whileso_iter_homo.
    by move=>j n m /gh /lefP Pnm; apply: whileso_iter_leso=>/=; apply: reps_leso=>i; apply: Pnm.
    by move=>i j; apply: qo_ubound.
  apply: eq_lim=>i; rewrite whileso_iter_limn.
  by apply/cvg_ex; exists (reps c gn).
  by f_equal; move: IH; rewrite vcvgn_limnE=>[[]].
- by move=>i /=.
Qed.

Lemma reps_limn c (g : nat -> fQO) :
  (nondecreasing_seq g) ->
  (forall i, cvgn (g ^~ i: nat -> 'SO)) -> 
    limn (fun i => reps c (g i)) = reps c (fun i => limn (g ^~ i: nat -> 'SO)).
Proof.
move=>P1 P2; move: (reps_cvgn (c := c) P1 P2).
by rewrite vcvgn_limnE=>[[]].
Qed.

Definition fQOlub (u : nat -> fQO) : fQO :=
  (fun i =>
    match (limn (fun n => u n i : 'SO)) \is cptn =P true with
    | ReflectT P => QOperation_Build P
    | _ => (0 : 'SO)
    end).

Lemma fQO_ge0 (g : fQO) : (((fun i => (0 : 'SO)) : fQO) <= g)%O.
Proof. by apply/lefP=>i; rewrite qoge0. Qed.

Lemma fQO_chaini (c : nat -> fQO) : cpo.chain c -> (forall i, cpo.chain (c ^~ i)).
Proof. by move=>Pc i m; move: (Pc m)=>/lefP; apply. Qed.

Lemma fQO_cvgni (c : nat -> fQO) i : cpo.chain c -> cvgn (c ^~ i : nat -> 'SO).
Proof.
move=>Pc; apply: (vnondecreasing_is_cvgn (b := b0)).
by apply/cpo.chain_homo/fQO_chaini. by move=>j; apply/qo_ubound.
Qed.

Lemma fQOEi (c : nat -> fQO) i : cpo.chain c ->
  fQOlub c i = limn (fun n => c n i : 'SO) :> 'SO.
Proof.
move=>Pc; rewrite /fQOlub.
have Pc3: [set x | x \is cptn] (limn (fun n => c n i : 'SO)).
  apply: (@closed_cvg _ _ _ eventually_filter (fun n => c n i : 'SO) _ _ _ _)=>//.
  by apply closed_isqo.
  by apply: nearW=>x; rewrite /= is_cptn.
  by apply/fQO_cvgni.
by case: eqP.
Qed.

Lemma fQOlub_ub : forall c : nat -> fQO, cpo.chain c -> (forall i, (c i <= fQOlub c)%O).
Proof.
move=>c Pc n; apply/lefP=>i; rewrite leEsub/= fQOEi//.
apply: nondecreasing_cvgn_lev.
by apply/cpo.chain_homo/fQO_chaini. by apply/fQO_cvgni.
Qed.

Lemma fQOlub_least : forall c : nat -> fQO, 
  cpo.chain c -> forall x : fQO, (forall i, (c i <= x)%O) -> (fQOlub c <= x)%O.
Proof.
move=>c Pc x Px; apply/lefP=>i; rewrite leEsub/= fQOEi//.
apply: limn_lev.
by apply/fQO_cvgni. by move=>n; move: (Px n)=>/lefP/(_ i).
Qed.

(* pointwise partial order is still a complete partial order *)
Import FunOrder.
HB.instance Definition _ := cpo.isCpo.Build FunOrder.fun_display
  fQO fQO_ge0 fQOlub_ub fQOlub_least.

(* semantic replacement is scott continuous *)
Lemma qo_fXs_scott : cpo.scott qo_fXs.
Proof.
split=>/=.
by move=>c Pc n/=; apply/lefP=>i; apply/fXs_leso.
move=>c Pc. apply/funext=>i; apply/val_inj=>/=.
rewrite /lub/= [RHS]fQOEi/=.
by move=>n; apply/lefP=>j/=; rewrite leEsub/=; apply/fXs_leso.
under eq_fun do rewrite (fQOEi _ Pc)/=.
symmetry. apply: reps_limn.
by apply/cpo.chain_homo.
by move=>j; apply: fQO_cvgni.
Qed.
HB.instance Definition _ := cpo.isScottContinuous.Build 
  _ _ _ _ qo_fXs qo_fXs_scott.

Lemma qo_fXs_chain : chain (chaini qo_fXs).
Proof.
elim=>[|n IH]/=; first by apply/le0c.
by apply/lefP=>j; rewrite leEsub/=; apply/fXs_leso.
Qed.

Lemma qo_fXs_lubE i : fsem (f i) = lub (chaini qo_fXs) i.
Proof.
rewrite fsem_repsnE /lub/=/QOCPO.qolub fQOEi.
  elim=>[|n IH]/=; first by apply/le0c.
  by apply/lefP=>j; rewrite leEsub/=; apply/fXs_leso.
rewrite -[RHS]limn_shiftS/=.
apply eq_lim=>n; elim: n i=>[//|n IH /= i].
by rewrite {1}/fXs; f_equal; apply/funext.
Qed.

(* Proposition 6.2 (2) *)
(* the least fixpoint *)
Lemma fsem_fX_lfp c : (forall i, fsem (c i) = fsem (fX c i)) -> 
  (forall i, fsem (f i) <= fsem (c i)).
Proof.
move=>P1 j.
have: qo_fXs (fun i => fsem (c i)) = (fun i => fsem (c i)).
  apply/funext=>i; apply/val_inj=>/=.
  by rewrite [RHS]P1 rep_reps.
move=>/least_fp_lub_chaini/lefP/(_ j).
by rewrite leEsub/= -qo_fXs_lubE.
Qed.

(* if program c doesn't contain proc call, then syntactic/semantic 
  replacement won't change its syntax/semantics *)
Lemma rep_no_callE c X : no_call_ c -> rep c X = c.
Proof.
elim: c=>//=.
by move=>c1 IH1 c2 IH2 =>/andP[] /IH1 -> /IH2 ->.
by move=>T fT x M c IH /forallP Pi; f_equal; apply/funext=>i; apply/IH/Pi.
by move=>T x M c IH /IH ->.
Qed.

Lemma reps_no_call c X : no_call_ c -> reps c X = fsem c.
Proof.
elim: c=>//=. 1-4: by intros; rewrite ?fsemE.
by move=>c1 IH1 c2 IH2 =>/andP[] /IH1 -> /IH2 ->; rewrite fsemE.
by move=>T fT x M c IH /forallP Pi; rewrite fsemE; f_equal; apply/funext=>i; apply/IH/Pi.
by move=>T x M c IH /IH ->; rewrite fsemE.
Qed.

End semantics2.
End Semantics.

HB.lock
Definition eq_fsem {F} f u1 u2 := @fsem F f u1 = @fsem F f u2.
Notation "c1 =c c2" := (@eq_fsem _ _ c1 c2) (at level 70).

Lemma eq_fsem_trans F f : 
  forall (a b c : @cmd_ F), eq_fsem f a b -> eq_fsem f b c -> eq_fsem f a c.
Proof. by rewrite eq_fsem.unlock; move=>a b c -> ->. Qed.
Lemma eq_fsem_refl F f : forall a : @cmd_ F, eq_fsem f a a.
Proof. by rewrite eq_fsem.unlock. Qed.
Lemma eq_fsem_sym F f : forall (a b : @cmd_ F), eq_fsem f a b -> eq_fsem f b a.
Proof. by rewrite eq_fsem.unlock; move=>a b ->. Qed.
Hint Extern 0 (@eq_fsem _ _ _ _) => (apply eq_fsem_refl) : core.

Add Parametric Relation F f : (@cmd_ F) (eq_fsem f)
  reflexivity proved by (@eq_fsem_refl F f)
  symmetry proved by (@eq_fsem_sym F f)
  transitivity proved by (@eq_fsem_trans F f)
  as eq_fsem_rel.

Module Export EQ_FSEM.
Require Import Setoid.

Add Parametric Morphism F f (T : qType) : (@init_ F T)
  with signature (@eq_qreg T) ==> (@eq _) ==> (@eq_fsem F f) as eq_fsem_init.
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
Add Parametric Morphism F f : (@circuit_ F)
  with signature eq_usem ==> (@eq_fsem F f) as eq_fsem_circuit.
Proof. by move=>x y; rewrite eq_fsem.unlock !fsemE eq_usem.unlock=>->. Qed.

Add Parametric Morphism F f : seqc_
  with signature (@eq_fsem F f) ==> (@eq_fsem F f) ==> (@eq_fsem F f) as eq_fsem_seqc.
Proof. by rewrite eq_fsem.unlock=>??+??+; rewrite !fsemE=>->->. Qed.

Add Parametric Morphism F f (T : qType) (FM : finType) : (@cond_ F T FM)
  with signature (@eq_qreg T) ==> (@eq _) ==> (@eq _) ==> (@eq_fsem F f) as eq_fsem_cond.
Proof.
move=>x y Pxy M ff; rewrite eq_fsem.unlock !fsemE.
by f_equal; apply/funext=>i; rewrite !liftf_funE !tm2mE 
  -(tf2f_eqr _ Pxy Pxy) liftf_lf_cast.
Qed.

Add Parametric Morphism F f T : (@cond2_ F T)
  with signature (@eq_qreg T) ==> (@eq _) ==> (@eq_fsem F f) ==> (@eq_fsem F f) ==> (@eq_fsem F f)
    as eq_fsem_cond2.
Proof.
move=>x y Pxy M c00 c01 + c10 c11 +.
by rewrite eq_fsem.unlock !fsemE -!(tf2f_eqr _ Pxy Pxy) !liftf_lf_cast=>->->.
Qed.

Add Parametric Morphism F f (T : qType) : (@while_ F T)
  with signature (@eq_qreg T) ==> (@eq _) ==> (@eq_fsem F f) ==> (@eq_fsem F f)
    as eq_fsem_while.
Proof.
move=>x y Pxy M c1 c2; rewrite eq_fsem.unlock !fsemE=>->.
by f_equal; apply/funext=>i; rewrite !liftf_funE !tm2mE 
  -(tf2f_eqr _ Pxy Pxy) liftf_lf_cast.
Qed.

Section AdditionalEQ.
Variable (FF : finType) (ff : proc_ FF).
Local Notation cmd_ := (@cmd_ FF).
Local Notation "c1 =c c2" := (@eq_fsem FF ff c1 c2).

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

Lemma eq_call i : <{[ call i ]}> =c ff i.
Proof. by rewrite eq_fsem.unlock fsemE. Qed.

Lemma eq_seqcl u1 u2 u3 :
  u1 =c u2 -> <{[ u1 ;; u3 ]}> =c <{[ u2 ;; u3 ]}>.
Proof. by move=>->. Qed.

Lemma eq_seqcr u1 u2 u3 :
  u1 =c u2 -> <{[ u3 ;; u1 ]}> =c <{[ u3 ;; u1 ]}>.
Proof. by move=>->. Qed.

Lemma eq_seqc u1 u2 u3 u4 :
  u1 =c u2 -> u3 =c u4 -> <{[ u1 ;; u3 ]}> =c <{[ u2 ;; u4 ]}>.
Proof. by move=>->->. Qed.

End AdditionalEQ.

End EQ_FSEM.

Lemma bigcup_const (I J: finType) (s : {set I}) (A : {set J}) :
  s != set0 -> \bigcup_(i in s) A = A.
Proof.
move=>/set0Pn[x Px]; apply/eqP; rewrite finset.eqEsubset; apply/andP; split.
by apply/bigcupsP. by apply: (bigcup_max x).
Qed.

Lemma bigcup_id (I : finType) (s : {set I}) :
  \bigcup_(i in s) [set i] = s.
Proof.
apply/setP=>i; apply/eqb_iff; split.
by move=>/bigcupP[j] Pj; rewrite inE=>/eqP->.
by move=>Pi; apply/bigcupP; exists i=>//; rewrite inE eqxx.
Qed. 

Lemma bigcup_subset I (r : seq I) (P : pred I) (J : finType) (f1 f2 : I -> {set J}) :
  (forall i, P i -> f1 i :<=: f2 i) -> 
    \bigcup_(i <- r | P i) f1 i :<=: \bigcup_(i <- r | P i) f2 i.
Proof.
by move=>IH; elim/big_rec2: _=>// i y1 y2 Pi Py; apply/finset.setUSS=>//; apply/IH.
Qed.

Lemma bigcup2 (I K : finType) J (r : seq J) (P : pred J) (fj : J -> {set I}) (fi : I -> {set K}) :
  \bigcup_(i in \bigcup_(j <- r | P j) fj j) fi i = \bigcup_(j <- r | P j) \bigcup_(i in fj j) fi i.
Proof.
elim: r=>[|a l IH]; first by rewrite !big_nil big_set0.
rewrite !big_cons; case: (P a)=>//.
by rewrite finset.bigcup_setU IH.
Qed.

Section Var.
Variable (F : finType) (f : proc_ F).
Local Notation cmd_ := (@cmd_ F).
Local Notation fsem := (@fsem F f).
Local Notation enum T := (isFinite.enum_subdef (Finite.class T)).

Fixpoint dep_vari (c : cmd_) : {set F} :=
  match c with
  | skip_ => set0
  | abort_ => set0
  | init_ _ _ _ => set0
  | circuit_ _ => set0
  | seqc_ c1 c2 => dep_vari c1 :|: dep_vari c2
  | cond_ _ fT _ _ fM => \bigcup_i dep_vari (fM i)
  | while_ _ _ _ c => dep_vari c
  | call_ i => [set i]
  end.

Definition explicit_dep i := dep_vari (f i).

Fixpoint dep_varn (s : {set F}) n :=
  match n with
  | 0 => s
  | S n => s :|: dep_varn (\bigcup_(i in s) (dep_vari (f i))) n
  end.

Lemma dep_varnU s1 s2 n :
  dep_varn (s1 :|: s2) n = dep_varn s1 n :|: dep_varn s2 n.
Proof.
elim: n s1 s2 =>//= n IH s1 s2.
by rewrite finset.bigcup_setU finset.setUACA IH.
Qed.

Lemma dep_varn0 n : dep_varn set0 n = set0.
Proof. by elim: n=>//= n Pn; rewrite big_set0 Pn finset.setU0. Qed.

Lemma dep_varn_bigcup I (r : seq I) (P : pred I) (fi : I -> {set F}) n :
  dep_varn (\bigcup_(i <- r | P i) fi i) n = 
    \bigcup_(i <- r | P i) dep_varn (fi i) n.
Proof.
elim/big_rec2: _; first by rewrite dep_varn0.
by move=>i y1 y2 Pi <-; rewrite dep_varnU.
Qed.

Lemma dep_varnE (s : {set F}) n :
  dep_varn s n.+1 = s :|: dep_varn (\bigcup_(i in s) (dep_vari (f i))) n.
Proof. by []. Qed.

Lemma dep_varnEV (s : {set F}) n :
  dep_varn s n.+1 = let s := dep_varn s n in 
                    s :|: \bigcup_(i in s) (dep_vari (f i)).
Proof.
elim: n s=>// n IH s.
rewrite dep_varnE IH/= finset.bigcup_setU !finset.setUA; f_equal; clear.
case: n=>[|n]/=; first by rewrite -finset.setUA finset.setUid.
by rewrite !finset.setUA -[RHS]finset.setUA finset.setUACA finset.setUid finset.setUAC.
Qed.

Definition implicit_dep i := dep_varn [set i] #|F|.

Lemma dep_varn_hom c : 
  {homo (dep_varn c) : m n / (m <= n)%N >-> (m :<=: n)}.
Proof.
suff: forall n, dep_varn c n :<=: dep_varn c n.+1.
  move=> cc x y /subnK => <-; elim: (y - x)%N => // n ih.
  by rewrite addSn; apply: (fintype.subset_trans ih); apply: cc.
move=>n; elim: n c=>[c /=|n /= IH c].
by rewrite finset.subsetUl.
apply/finset.setUS/IH.
Qed.

Lemma dep_varn_eq c n :
  dep_varn c n.+1 = dep_varn c n ->
    forall i, dep_varn c (i + n)%N = dep_varn c n.
Proof.
move=>P1; elim=>// i Pi.
by rewrite addSn dep_varnEV Pi /= -[RHS]P1 dep_varnEV/=.
Qed.

Lemma dep_varn_max c :
  dep_varn c #|F|.+1 = dep_varn c #|F|.
Proof.
apply/eqP; case: eqP=>// /eqP Pf.
have: forall i, (i <= #|F|.+1)%N -> (i <= #|dep_varn c i|)%N.
  elim=>// i IH Pi. move: {+}Pi=>/ltnW/IH=>P1; apply: (leq_ltn_trans P1).
  move: (dep_varn_hom c (leqnSn i))=>/subset_leqif_cards/leqifP.
  case: eqP=>// /esym P2. 
  move: P2 {+}P2 Pf=>/dep_varn_eq/(_ (#|F| -i)%N) + /dep_varn_eq/(_ (#|F| - i).+1).
  by rewrite addSn subnK// =><-->; rewrite eqxx.
move=>/(_ (#|F|.+1))/(_ (leqnn _)).
move: (@finset.subsetT _ (dep_varn c #|F|.+1))=>/subset_leqif_cards.
by rewrite cardsT=>P1 P2; move: (leq_ltn_trans P1 P2); rewrite ltnn.
Qed.

(* Lemma test8 i : i \in (implicit_dep i).
Proof.
move: (fintype0 i)=>/eqP; rewrite -lt0n=>/(dep_varn_hom [set i])/fintype.subsetP/(_ i).
apply. by rewrite/= !inE eqxx.
Qed. *)

Lemma implicit_depE i : implicit_dep i = 
  i |: \bigcup_(j in dep_vari (f i)) implicit_dep j.
Proof.
by rewrite /implicit_dep -dep_varn_max/= big_set1 -dep_varn_bigcup bigcup_id.
Qed.

Fixpoint explicit_vset (c : cmd_) :=
  match c with
  | skip_ => set0
  | abort_ => set0
  | init_ _ x _ => mset x
  | circuit_ u => ucmd_vset u
  | seqc_ c1 c2 => explicit_vset c1 :|: explicit_vset c2
  | cond_ _ fT x _ fM => mset x :|: \bigcup_i explicit_vset (fM i)
  | while_ _ x _ c => mset x :|: explicit_vset c
  | call_ i => set0
  end.

Definition cmd_vset (c : cmd_) :=
  explicit_vset c :|: 
    \bigcup_(i in dep_vari c) \bigcup_(j in implicit_dep i) explicit_vset (f j).

Lemma cmd_vset_skipE : cmd_vset skip_ = set0.
Proof. by rewrite /cmd_vset/= big_set0 finset.setU0. Qed.

Lemma cmd_vset_abortE : cmd_vset abort_ = set0.
Proof. by rewrite /cmd_vset/= big_set0 finset.setU0. Qed.

Lemma cmd_vset_initE T (x : qreg T) U : cmd_vset (init_ x U) = mset x.
Proof. by rewrite /cmd_vset/= big_set0 finset.setU0. Qed.

Lemma cmd_vset_circuitE u : cmd_vset (circuit_ u) = ucmd_vset u.
Proof. by rewrite /cmd_vset/= big_set0 finset.setU0. Qed.

Lemma cmd_vset_seqE c1 c2 : cmd_vset (seqc_ c1 c2) = cmd_vset c1 :|: cmd_vset c2.
Proof. by rewrite /cmd_vset/= finset.bigcup_setU finset.setUACA. Qed.

Lemma cmd_vset_condE T fT (x : qreg T) (M : 'QM(fT; 'Ht T)) ff : 
  cmd_vset (cond_ x M ff) = mset x :|: \bigcup_i (cmd_vset (ff i)).
Proof. by rewrite /cmd_vset/= big_split/= finset.setUA bigcup2. Qed.

Lemma cmd_vset_cond2E T (x : qreg T) (M : 'QM(bool; 'Ht T)) c0 c1 : 
  cmd_vset (cond2_ x M c0 c1) = mset x :|: (cmd_vset c0) :|: (cmd_vset c1).
Proof.
by rewrite cond2_.unlock cmd_vset_condE big_bool/= 
  [X in _ :|: X]finset.setUC finset.setUA.
Qed.

Lemma cmd_vset_whileE T (x : qreg T) (M : 'QM(bool; 'Ht T)) c : 
  cmd_vset (while_ x M c) = mset x :|: (cmd_vset c).
Proof. by rewrite /cmd_vset/= finset.setUA. Qed.

Lemma cmd_vset_callE i : cmd_vset (call_ i) = cmd_vset (f i).
Proof.
by rewrite /cmd_vset/= finset.set0U big_set1 implicit_depE finset.bigcup_setU big_set1 bigcup2.
Qed.

Definition cmd_vsetE := (cmd_vset_skipE, cmd_vset_abortE, 
  cmd_vset_initE, cmd_vset_initE, cmd_vset_seqE, cmd_vset_circuitE,
  cmd_vset_cond2E, cmd_vset_condE, cmd_vset_whileE, cmd_vset_callE).

Lemma fsem_local_no_call c : 
  no_call_ c -> exists E : 'SO_(cmd_vset c), fsem c = liftfso E.
Proof.
elim: c=>//=.
by exists \:1; rewrite fsemE liftfso1.
by exists (0 : 'SO); rewrite fsemE linear0.
by move=>T q v; rewrite cmd_vsetE; exists (initialso (tv2v q v)); rewrite fsemE.
- move=>u; move: (usem_local u)=>[U PU]; rewrite cmd_vsetE.
  by exists (formso U); rewrite fsemE PU liftfso_formso.
- move=>c1 P1 c2 P2 /andP[] /P1 [E1 IH1] /P2 [E2 IH2]; rewrite cmd_vsetE.
  exists (liftso (finset.subsetUr _ _) E2 :o liftso (finset.subsetUl _ _) E1).
  by rewrite fsemE IH1 IH2 liftfso_comp !liftfso2.
- move=>T fT x M c IH /forallP Pi; rewrite cmd_vsetE.
  pose ci i : 'SO_(\bigcup_i cmd_vset (c i)) := 
    liftso (finset.bigcup_sup i is_true_true) (projT1 (cid (IH i (Pi i)))).
  have P3i i : fsem (c i) = liftfso (ci i)
    by rewrite /ci liftfso2; move: (projT2 (cid (IH i (Pi i)))).
  exists (ifso (lift_fun (finset.subsetUl _ _) (tm2m x x M)) 
      (fun i : fT => liftso (finset.subsetUr _ _) (ci i))).
  rewrite fsemE liftfso_ifso liftf_fun2.
  by under [in RHS]eq_fun do rewrite liftfso2 -P3i.
- move=>T x M c P /P [E IH]; rewrite cmd_vsetE.
  exists (whileso (lift_fun (finset.subsetUl _ _) (tm2m x x M)) 
    true (liftso (finset.subsetUr _ _) E)).
  move: (fsem_qo f c); rewrite IH liftfso_qoE=>PE.
  by rewrite fsemE (QOperation_BuildE PE) liftfso_whileso/= liftf_fun2 liftfso2 IH.
Qed.

Lemma cmd_vset_explicitE c (fi : F -> cmd_) :
  cmd_vset (rep c fi) = 
    explicit_vset c :|: \bigcup_(i in dep_vari c) cmd_vset (fi i).
Proof.
elim: c=>//=.
by rewrite cmd_vsetE big_set0 finset.setU0.
by rewrite cmd_vsetE big_set0 finset.setU0.
by move=>T q v; rewrite cmd_vsetE big_set0 finset.setU0.
by move=>u; rewrite cmd_vsetE big_set0 finset.setU0.
by move=>c1 IH1 c2 IH2; rewrite cmd_vsetE IH1 IH2 finset.setUACA finset.bigcup_setU.
- move=>T fT x M ff IH; rewrite cmd_vsetE bigcup2 -finset.setUA -big_split/=.
  by f_equal; apply eq_bigr.
- by move=>T x M c IH; rewrite cmd_vsetE IH finset.setUA.
- by move=>i; rewrite big_set1 finset.set0U.
Qed.

Lemma repn_vset_le c i : cmd_vset (repn f c i) :<=: cmd_vset c.
Proof.
elim: c i=>//=.
1-4: by intros; case: i.
- by move=>c1 IH1 c2 IH2 i; rewrite repnE !cmd_vsetE; apply/finset.setUSS.
- move=>T fT x M ff IH n; rewrite repnE !cmd_vsetE finset.setUS//.
  by apply/bigcup_subset.
- by move=>T x M c IH i; rewrite repnE !cmd_vsetE finset.setUS.
- move=>i; case=>/=[|n]; first by rewrite !cmd_vsetE ?finset.sub0set//.
  elim: n i=>[/= i|n IH i].
  rewrite cmd_vset_explicitE !cmd_vsetE /cmd_vset; apply/finset.setUSS=>//.
  by apply/bigcup_subset=>??; apply finset.sub0set.
  rewrite/= cmd_vset_explicitE !cmd_vsetE {2}/cmd_vset; apply/finset.setUSS=>//.
  apply/bigcup_subset=>j _; apply: (fintype.subset_trans (IH _)).
  by rewrite /cmd_vset/= finset.set0U big_set1.
Qed.

Lemma liftfso_is_cvgnE (S : {set mlab}) (fi : nat -> 'SO[msys]_S) :
  cvgn fi = cvgn (fun i => liftfso (fi i)).
Proof.
rewrite propeqE; split; first by apply: linear_is_cvg.
move=>/cauchy_seqP P. apply/cauchy_seqP=>e egt0.
move: (P _ egt0)=>[N] P1; exists N=>s t Ps Pt.
move: (P1 _ _ Ps Pt); apply: le_lt_trans.
rewrite -linearB/=; apply: liftfso_norm.
Qed.

Lemma liftfso_limnE (S : {set mlab}) (fi : nat -> 'SO[msys]_S) :
  limn (fun i => liftfso (fi i)) = liftfso (limn fi).
Proof.
case: (asboolP (cvgn fi))=>Pc; first by rewrite linear_lim.
move: Pc {+}Pc => /dvgP {2}->; rewrite liftfso_is_cvgnE=>/dvgP->.
by rewrite /witness/= linear0.
Qed.

Lemma fsem_no_callE c : 
  no_call_ c -> fsem c = fsem_no_call c.
Proof.
elim: c=>//=; intros; rewrite ?fsemE//.
by move: H1=>/andP[]/H->/H0->.
by f_equal; apply/funext=>i; apply/H; move: H0=>/forallP.
by rewrite H.
Qed.

Lemma fsem_local c : exists E : 'SO_(cmd_vset c), fsem c = liftfso E.
Proof.
rewrite fsem.unlock.
pose s i := liftso (repn_vset_le _ i) 
  (projT1 (cid (fsem_local_no_call (repn_no_call f c i)))).
exists (limn s).
rewrite -liftfso_limnE; apply eq_lim=>i.
rewrite /s liftfso2/=.
move: (projT2 (cid (fsem_local_no_call (repn_no_call f c i))))<-.
by rewrite fsem_no_callE// repn_no_call.
Qed.

(* Computable definition *)
(* Fixpoint deps_vari (c : cmd_) : seq F :=
  match c with
  | skip_ => [::]
  | abort_ => [::]
  | init_ _ _ _ => [::]
  | circuit_ _ => [::]
  | seqc_ c1 c2 => undup (dep_vari c1 ++ dep_vari c2)
  | cond_ _ fT _ _ fM => undup (flatten [seq dep_vari (fM i) | i <- enum fT])
  | while_ _ _ _ c => dep_vari c
  | call_ i => [:: i]
  end.

Definition explicit_deps i := dep_vari (f i).

Fixpoint deps_varn (s1 s2 : seq F) n : seq F :=
  match n with
  | 0 => s2
  | S n => let s := seq.filter (fun i => i \notin s2) (undup (flatten (map explicit_dep s1))) in
           dep_varn s (undup (s2 ++ s)) n
  end.

Definition implicit_deps i := dep_varn [:: i] [::] #|F|.

Lemma eq_deps i : implicit_deps i =i implicit_dep i.
*)

(* syntactically compute the disjointness of two programs *)
Fixpoint cmd_var_explicit_disj T (x : qreg T) (c : cmd_) :=
    match c with
    | skip_ | abort_ => true
    | init_ _ y _ => disjoint_qreg x y
    | circuit_ u => ucmd_var_disj x u
    | cond_ _ F y _ f => disjoint_qreg x y && [forall i : F, cmd_var_explicit_disj x (f i)]
    | while_ _ y _ c => disjoint_qreg x y && cmd_var_explicit_disj x c
    | seqc_ c1 c2 => cmd_var_explicit_disj x c1 && cmd_var_explicit_disj x c2 
    | call_ _ => true
    end.
Definition cmd_var_disj T (x : qreg T) (c : cmd_) :=
  cmd_var_explicit_disj x c && 
    [forall i in dep_vari c,
      [forall j in implicit_dep i, cmd_var_explicit_disj x (f j)]].

Fixpoint cmd_ucmd_disj (u : ucmd_) (c : cmd_) :=
    match u with
    | uskip_ => true
    | unitary_ _ y _ => cmd_var_disj y c 
    | sequ_ u1 u2 => cmd_ucmd_disj u1 c && cmd_ucmd_disj u2 c 
    | qcond_ _ F y _ fu => cmd_var_disj y c && [forall i : F, cmd_ucmd_disj (fu i) c]
    end.

Fixpoint cmd_explicit_disj (c1 c2 : cmd_) :=
    match c1 with
    | skip_ | abort_     => true
    | init_ _ x _ => cmd_var_disj x c2
    | circuit_ u  => cmd_ucmd_disj u c2
    | seqc_ c11 c12 => cmd_explicit_disj c11 c2 && cmd_explicit_disj c12 c2
    | cond_ _ _ x _ f => cmd_var_disj x c2 && [forall i, cmd_explicit_disj (f i) c2]
    | while_ _ x _ c1 => cmd_var_disj x c2 && cmd_explicit_disj c1 c2
    | call_ _ => true
    end.
Definition cmd_disj (c1 c2 : cmd_) :=
  cmd_explicit_disj c1 c2 && 
    [forall i in dep_vari c1,
      [forall j in implicit_dep i, cmd_explicit_disj (f j) c2]].

Lemma cmd_var_disjP T (x : qreg T) (c : cmd_) :
    cmd_var_disj x c -> [disjoint mset x & cmd_vset c].
Proof.
elim: c=>/=.
1,2: by rewrite cmd_vsetE disjointX0.
by move=>???; rewrite cmd_vsetE -disj_setE=>/andP[]/=.
by move=>?; rewrite cmd_vsetE=>/andP/=[]/ucmd_var_disj_vsetP.
- move=>? IH1 ? IH2; rewrite cmd_vsetE=>/andP[]/=/andP[] P1 P2 /forallP P3.
  rewrite disjointXU IH1 ?IH2//; apply/andP; split=>//; apply/forallP=>i;
  by apply/implyP=>Pi; move: (P3 i); rewrite inE Pi//= orbT.
- move=>???? fu IH; rewrite cmd_vsetE=>/andP[]/=/andP[] Pxy /forallP Pi /forallP P.
  rewrite disjointXU -disj_setE Pxy/=; apply/bigcup_disjoint=>i _; apply/IH/andP; split=>//.
  by apply/forallP=>j; apply/implyP=>Pj; move: (P j)=>/implyP; apply; apply/bigcupP; exists i.
- move=>???? IH; rewrite cmd_vsetE disjointXU -disj_setE;
  by move=>/andP[]/=/andP[]->/= P1 P2; apply/IH/andP.
move=>i /andP[]/= _ /forallP P; rewrite /cmd_vset/= finset.set0U big_set1.
apply/bigcup_disjoint=>j Pj.
move: (P i); rewrite inE eqxx/==>/forallP/(_ j); rewrite Pj/=; clear.
elim: (f j)=>/=.
1,2,8: by rewrite disjointX0.
by move=>???; rewrite -disj_setE.
by move=>? /ucmd_var_disj_vsetP.
by move=>? IH1 ? IH2/andP[]/IH1+/IH2; rewrite disjointXU=>->->.
- move=>????? IH/andP[] + /forallP P2; rewrite disjointXU -disj_setE=>->/=.
  by apply/bigcup_disjoint=>i _; apply/IH/P2.
- by move=>???? IH /andP[]; rewrite disjointXU -disj_setE=>->/=.
Qed.

Lemma cmd_ucmd_disjP u c :
  cmd_ucmd_disj u c -> [disjoint ucmd_vset u  & cmd_vset c].
Proof.
elim: u.
by rewrite /= disjoint0X.
by move=>???/=/cmd_var_disjP.
by move=>u1 IH1 u2 IH2/=/andP[] /IH1 + /IH2; rewrite disjointUX=>->->.
move=>?? x ? g IH /=/andP[]/cmd_var_disjP + /forallP Pi.
rewrite disjointUX=>->/=; rewrite disjoint_sym; apply/bigcup_disjoint=>i _.
by rewrite disjoint_sym; apply/IH/Pi.
Qed.

Lemma cmd_disjP c1 c2 :
    cmd_disj c1 c2 -> [disjoint cmd_vset c1 & cmd_vset c2].
Proof.
elim: c1.
1,2: by rewrite cmd_vsetE disjoint0X.
by move=>???; rewrite cmd_vsetE=>/andP/=[]/cmd_var_disjP.
by move=>?; rewrite cmd_vsetE=>/andP/=[]/cmd_ucmd_disjP.
- move=>? IH1 ? IH2; rewrite cmd_vsetE=>/andP[]/=/andP[] P1 P2 /forallP P3.
  rewrite disjointUX IH1 ?IH2//; apply/andP; split=>//; apply/forallP=>i;
  by apply/implyP=>Pi; move: (P3 i); rewrite inE Pi//= orbT.
- move=>???? fu IH; rewrite cmd_vsetE=>/andP[]/=/andP[] Pxy /forallP Pi /forallP P.
  rewrite disjointUX cmd_var_disjP//= disjoint_sym bigcup_disjoint// =>i _.
  rewrite disjoint_sym IH//; apply/andP; split=>//.
  by apply/forallP=>j; apply/implyP=>Pj; move: (P j)=>/implyP; apply; apply/bigcupP; exists i.
- move=>???? IH; rewrite cmd_vsetE disjointUX.
  by move=>/andP[]/=/andP[]/cmd_var_disjP->/= P1 P2; apply/IH/andP.
move=>i /andP[]/= _ /forallP /(_ i); rewrite inE eqxx/= {1}/cmd_vset/= finset.set0U big_set1=>/forallP P.
rewrite disjoint_sym; apply/bigcup_disjoint=>j Pj; rewrite disjoint_sym.
move: (P j); rewrite Pj/=; clear.
elim: (f j)=>/=.
1,2,8: by rewrite disjoint0X.
by move=>???/cmd_var_disjP.
by move=>? /cmd_ucmd_disjP.
by move=>? IH1 ? IH2/andP[]/IH1+/IH2; rewrite disjointUX=>->->.
- move=>????? IH/andP[]/cmd_var_disjP + /forallP P2; rewrite disjointUX=>->/=.
  by rewrite disjoint_sym; apply/bigcup_disjoint=>i _; rewrite disjoint_sym; apply/IH/P2.
- by move=>???? IH /andP[]/cmd_var_disjP; rewrite disjointUX=>->/=.
Qed.

End Var.

Section QRecuisiveLaw.
Variable (FF : finType) (ff : proc_ FF).
Local Notation cmd_ := (@cmd_ FF).
Local Notation fsem := (@fsem FF ff).
Local Notation "c1 =c c2" := (@eq_fsem FF ff c1 c2).

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
    <{[ [x] := NormalState.clone _ (sc (phi : 'Ht T)) _ ]}>.
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
suff ->: (init_ x ((ONB.clone _ _ (onb_swap phi) _)true)) =c (init_ x (phi false)) by [].
by apply eq_init=>/=.
Qed.

(* proposition 5.1 (4) : initialization law, if-elimination *)
Lemma init_ifTK T (x : 'QReg[T]) (psi : 'NS('Ht T)) c0 c1 :
  <{[ ([x] := psi) ;; (c0 ◁ '[| psi >][x] ▷ c1) ]}> =c 
    <{[ ([x] := psi) ;; c1 ]}>.
Proof.
rewrite eq_fsem.unlock !fsemE linearDl/= -!comp_soA -!liftfso_formso -!liftfso_comp -[RHS]addr0.
do ! f_equal.
apply/superopP=>y. rewrite soE initialsoE formsoE linearZr/= linearZl/=; f_equal.
by rewrite tf2f_adj adj_outp tv2v_out !tf2f_comp outp_comp ns_dot scale1r outp_comp ns_dot scale1r.
set t := formso _ :o _; suff ->: t = 0 by rewrite linear0 comp_so0r.
by apply/superopP=>y; rewrite /t soE initialsoE !soE linearZr/= tv2v_out tf2f_comp 
  linearBl/= outp_comp ns_dot scale1r comp_lfun1l subrr linear0 scaler0 comp_lfun0l.
Qed.

Lemma init_ifFK (x : qreg Bool) (phi psi : 'NS('Ht Bool)) c0 c1 :
  [< (phi : 'Ht _); (psi : 'Ht _) >] = 0 ->
  <{[ ([x] := phi) ;; (c0 ◁ '[| psi >][x] ▷ c1) ]}> =c 
    <{[ ([x] := phi) ;; c0 ]}>.
Proof.
move=>P.
rewrite eq_fsem.unlock !fsemE linearDl/= -!comp_soA -!liftfso_formso -!liftfso_comp -[RHS]add0r.
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
  {H : `{{forall i, cmd_var_disj ff <{(x1,x2)}> (P i)}}} :
    <{[ If tmeas[x1] = m then P m fI ;; [(x1,x2)] := phi ]}> =c
      <{[ If tmeas[(x1,x2)] = k then P k.1 fI ;; [(x1,x2)] := phi ]}>.
Proof.
move: Hx; rewrite /cmd_expose=>Hx.
rewrite eq_fsem.unlock !fsemE !ifso_elem pair_bigV/= !linear_sumr/=.
apply eq_bigr; rewrite -/evalQT=>i _.
rewrite -linear_sumr/= !comp_soA.
move: (fsem_local ff (P i))=>[E ->]; rewrite liftfso_compC ?cmd_var_disjP//.
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
  <{[ c ◁ M[x] ▷ c ]}> =c <{[ ('[ M[x] ]) ;; c ]}>.
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
Lemma seqcC (c1 c2 : cmd_) {H : `{{cmd_disj ff c1 c2}}} :
  <{[ c1 ;; c2 ]}> =c <{[ c2 ;; c1 ]}>.
Proof.
rewrite eq_fsem.unlock !fsemE.
move: (fsem_local ff c1) (fsem_local ff c2)=>[U1 ->][U2 ->].
by rewrite liftfso_compC // disjoint_sym cmd_disjP.
Qed.

(* proposition 5.4 (3) : sequential composition, associativity *)
Lemma seqcA c0 c1 c2 :
  <{[ c0 ;; c1 ;; c2 ]}> =c <{[ c0 ;; (c1 ;; c2) ]}>.
Proof. by rewrite eq_fsem.unlock !fsemE comp_soA. Qed.

(* proposition 5.4 (4) : sequentiality *)
Lemma if_seqc T (x : 'QReg[T]) (P : {hspace 'Ht T}) c0 c1 c2 c3 
  {H0 : `{{ cmd_var_disj ff x c0 }}} {H1 : `{{ cmd_var_disj ff x c1 }}} :
  let M := pmeas P in
  <{[ (c0 ◁ M[x] ▷ c1) ;; (c2 ◁ M[x] ▷ c3) ]}> =c 
    <{[ (c0 ;; c2) ◁ M[x] ▷ (c1 ;; c3) ]}>.
Proof.
move=>M. move: (fsem_local ff c0) (fsem_local ff c1) => [e0 P0] [e1 P1].
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
Lemma seqc_distrr T (x : qreg T) M c0 c1 c {H : `{{cmd_var_disj ff x c}}} :
  <{[ c ;; (c0 ◁ M[x] ▷ c1) ]}> =c <{[ (c ;; c0) ◁ M[x] ▷ (c ;; c1) ]}>.
Proof.
move: (fsem_local ff c)=>[y Py].
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

(* in Section 6.1 *)
Lemma while_of_call T (x : 'QReg[T]) M P i {H : `{{no_call_ P}}}: 
  ff i = <{[ M[x] ▷ (P ;; (call i)) ]}> ->
    <{[ M[x] * P ]}> =c ff i.
Proof.
move=>Pf; rewrite eq_fsem.unlock [RHS]fsem_repsnE fsem_whileE
  whileso.unlock -[in LHS]limn_shiftS.
apply: eq_lim; elim=>[//=|n IH].
  by rewrite Pf/= cond2_.unlock/= !(ifso_bool true)/= !(reps_no_call ff).
rewrite Pf/= cond2_.unlock/= (ifso_bool true)/=.
by move: IH=>/=->; rewrite (ifso_bool true)/= !(reps_no_call ff).
Qed.

(* Theorem 6.1, tail recursive *)
Lemma tail_recursive T (x : 'QReg[T]) M P Q i {HP : `{{no_call_ P}}} {HQ : `{{no_call_ Q}}} : 
  ff i = <{[ Q ◁ M[x] ▷ (P ;; (call i)) ]}> ->
    <{[ (M[x] * P) ;; Q ]}> =c ff i.
Proof.
move=>Pf; rewrite eq_fsem.unlock [RHS]fsem_repsnE !fsemE whileso.unlock.
rewrite -so_comp_limr; first by apply: whileso_is_cvg.
rewrite -[in LHS]limn_shiftS.
apply: eq_lim; elim=>[//=|n IH].
  by rewrite Pf/= cond2_.unlock/= !(ifso_bool true)/= 
    !(reps_no_call ff)// !comp_so0l !add0r comp_so1l.
rewrite Pf/= cond2_.unlock/= (ifso_bool true)/=;
rewrite comp_soDr !comp_soA; move: IH=>/=->; 
by rewrite (ifso_bool true)/= !(reps_no_call ff)// comp_so1r.
Qed.

End QRecuisiveLaw.

(* TODO : add automation for solving cmd_expose *)