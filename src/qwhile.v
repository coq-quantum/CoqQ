From mathcomp Require Import all_ssreflect all_algebra complex.
Require Import forms.
From mathcomp.analysis Require Import boolp reals.
From mathcomp.real_closed Require Import complex.
Require Import Relation_Definitions Setoid.
(* several lemma in classical_sets and finset have the same name. *)

Require Import mcextra hermitian prodvect tensor mxtopology setdec lfundef quantum inhabited dirac.
Import Order.TTheory GRing.Theory Num.Theory ComplexField Num.Def complex.
Import Vector.InternalTheory.
Local Notation C := hermitian.C.
Local Open Scope set_scope.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

(******************************************************************************)
(* This file provide the definition of qwhile language                        *)
(*   suppose L is the finType of label for the whole space                    *)
(*   H is L -> chsType, i.e., each label corresponds to a Hilbert space       *)
(* -------------------------------------------------------------------------- *)
(*  Concrete syntax for qwhile language (shallow embedding, not limited)      *)
(*  for loops :  (notation for \big[seq_/skip]_(<range> | <condition>) F      *)
(*      [ for <range> 'do' F ]                                                *)
(*      [ for <range> | <condition> 'do' F ]                                  *)
(*  - <range> : from mathcomp/ssreflect/bigop.v                               *)
(*    (i <- s)     i ranges over the sequence s.                              *)
(*    (m <= i < n) i ranges over the nat interval m, m+1, ..., n-1.           *)
(*    (i < n)      i ranges over the (finite) type 'I_n (i.e., ordinal n).    *)
(*    (i : T)      i ranges over the finite type T.                           *)
(*    i or (i)     i ranges over its (inferred) finite type.                  *)
(*    (i in A)     i ranges over the elements that satisfy the collective     *)
(*                 predicate A (the domain of A must be a finite type).       *)
(*  initialization                                                            *)
(*      [it x := v ] : x : vars T, v : 'Hs T                                  *)
(*                     (v should have cononical to 'NS)                       *)
(*  unitary transformation                                                    *)
(*      [ut x := U ] : x : vars T, U : 'End[T]                                *)
(*                     (U should have cononical to 'FU)                       *)
(*      [ut [x , y] := U ] : x : vars T1, y : vars T2, U : 'End[T1*T2]        *)
(*                     (U should have cononical to 'FU)                       *)
(*  if statement                                                              *)
(*      [if M [x] = t then F ] : x : vars T, M : I -> 'End[T]                 *)
(*                     (M should have cononical to 'QM)                       *)
(*      [if tmeas[x] = t then F ] : x : vars T                                *)
(*                     computational measurement as guard                     *)
(*      [if M [x, y] = t then F ] : x : vars T1, y : vars T2,                 *)
(*                     M : I -> 'End[T1*T2]                                   *)
(*                     (M should have cononical to 'QM)                       *)
(*      [if tmeas[x , y] = t then F ] : x : vars T1, y : vars T2              *)
(*                     computational measurement as guard                     *)
(*  while                                                                     *)
(*      [while M [x] = b do C ] : x : vars T, M : bool -> 'End[T]             *)
(*                     (M should have cononical to 'QM)                       *)
(*      [while tmeas[x] = b do C ] : x : vars bool, b : bool                  *)
(*                     computational measurement as guard                     *)
(*      [while M [x, y] = b do C ] : x : vars T1, y : vars T2,                *)
(*                     M : I -> 'End[T1*T2]                                   *)
(*                     (M should have cononical to 'QM)                       *)
(* -------------------------------------------------------------------------- *)
(* Mechanism of quantum variable                                              *)
(* - x : vars T == declare variable of type T, T is ihbFinType                *)
(* - x : vars bool == declare qubit                                           *)
(* - variable asscoicates a ihbFinType T and the corresponding                *)
(*       subsystem (vset x) : {set L}                                         *)
(*       (with a bijection vt2i : T -> 'Idx[H]_S which is hide to user).      *) 
(*       the Hilbert space is 'H[H]_(vset x).                                 *)
(* - bijection vt2i is used to ensure that, if we pack several vars together, *)
(*       the action on the packing type is consistent to the separate action. *)
(* - pvars2 x y : vars (T1 * T2) if (x : vars T1) (y : vars T2)               *)
(* - pvars_tuple x : vars (n.-tuple T) if x : n.-tuple (vars T)               *)
(* - pvars_ffun x : vars {ffun I -> T} if x : I -> vars T                     *)
(* - pvars_dffun x : vars {dffun forall i : I -> T i}                         *)
(*       if x : forall i : I, vars (T i)                                      *)
(* pvars require the disjointness condition, i.e.,                            *)
(*       [disjoint (vset (x i)) & (vset (x j))] if i != j                     *)
(* -------------------------------------------------------------------------- *)
(* definition of injection. E.g., x : vars bool, v : 'Hs bool (the Hilbert    *)
(*   space of qubit, but not relate to H), (tv2v x v) then inject v to the    *)
(*   variable x, that is, |v>_x (in qexpr scope). For simple use, injection   *)
(*   for two variables is also defined, as tv2v2 / tf2f2                      *)
(* -------------------------------------------------------------------------- *)
(* definition of Hoare triples, global form (lfun), local form (lfun), qexpr  *)
(*   form (qexpr), state form (qexpr, when everything is vector, instead      *)
(*   of writing |v><v|, we can simply write |v> )                             *)
(*   relation : state <-> qexpr <-> local -> global                           *)
(*   Hoare triple also has two bool parameters,                               *)
(*        pt = true (total correctness)                                       *)
(*        pt = false (partial correctness),                                   *)
(*        st = true (saturated, = ),                                          *)
(*        st = false (may not saturated, <= ),                                *)
(*   since most of the rules are the same for both total and partial          *)
(*   correctness, and rules for skip, unitary trans and initialization are    *)
(*   saturated (also the most frequenct constructs) with the help of pt and   *)
(*   st, we don't need to duplicate rules                                     *)
(* -------------------------------------------------------------------------- *)
(* Utility : lemmas of rewriting quantum expressions with types               *)
(*   e.g., ⌈ M ; x ⌉ ∘ ｜ v ; x 〉 = ｜ M v ; x 〉                             *)
(*   we also show that packing variables act as we desired, e.g.,             *)
(*   ｜ u ⊗t v ; pvars2 x y〉 = ｜ u ⊗t v ; (x , y) 〉                      *)
(*   ｜ tentv_ffun v ; pvars_ffun x 〉 = \tens_i｜ v i ; x i 〉               *)
(******************************************************************************)


Lemma natrS_neq0 (T : numDomainType) n : (n.+1%:R : T) != 0.
Proof. by rewrite pnatr_eq0. Qed.
Global Hint Extern 0 (is_true (_.+1%:R != 0)) => solve [apply: natrS_neq0] : core.
Global Hint Extern 0 (is_true (0 <= _%:R)) => solve [apply: ler0n] : core.
Global Hint Extern 0 (is_true (0 < _.+1%:R)) => solve [apply: ltr0Sn] : core.
Lemma natr_nneg (F : numDomainType) n : (n%:R : F) \is Num.nneg.
Proof. by rewrite nnegrE. Qed.
Global Hint Extern 0 (is_true (_%:R \is Num.nneg)) => solve [apply: natr_nneg] : core.

Global Hint Resolve leq_ord : core.
Global Hint Extern 0 (is_true (uniq (index_enum _))) => solve [apply: index_enum_uniq] : core.

Section QWhile.
Context (L : finType) (H : L -> chsType).
(* Check 'F[H]_setT. *)

Section Syntax.
(* Check 'F[H]_set0. *)

Inductive cmd_ : Type :=
| abort_
| skip_
| init_              (S : {set L}) of 'NS[H]_S 
| unitary_           (S : {set L}) of 'FU[H]_S
| cond_ (f: finType) (S : {set L}) of 'QM[H]_(f;S) & (f -> cmd_)
| while_             (S : {set L}) of 'QM[H]_(bool;S) & bool & cmd_
| seqc_                   of cmd_ & cmd_.

Fixpoint while_iter_ (S : {set L}) (M:'QM[H]_(bool;S)) (b : bool) (c: cmd_) n : cmd_:=
  match n with
  | O => abort_
  | S n => cond_ M (fun b':bool => 
                    if b' == b then seqc_ c (while_iter_ M b c n)
                    else skip_)
  end.

End Syntax.

Section Semantics.

Fixpoint fvars (c : cmd_) : {set L} :=
  match c with
  | abort_ =>set0
  | skip_ => set0
  | init_ s v => s 
  | unitary_ s U => s
  | cond_ F s M fc => s :|: \bigcup_i (fvars (fc i))
  | while_ s M b c => s :|: (fvars c)
  | seqc_ c1 c2 => (fvars c1) :|: (fvars c2)
  end.

Fixpoint fsem_aux (c : cmd_) : 'SO[H]_setT := 
  match c with
  | abort_          => 0
  | skip_           => :1
  | init_ s v       => liftfso (initialso v)
  | unitary_ _ U    => liftfso (unitaryso U)
  | cond_ F s M fc  => ifso (liftf_fun M) (fun i : F => fsem_aux (fc i))
  | while_ s M b c    => whileso (liftf_fun M) b (fsem_aux c)
  | seqc_ c1 c2     => (fsem_aux c2) :o (fsem_aux c1)
  end.

Definition fsem_r c := fsem_aux c.
Fact fsem_key : unit. Proof. by []. Qed.
Definition fsem := locked_with fsem_key fsem_r.
Canonical fsem_unlockable := [unlockable fun fsem].

Lemma fsem_abortE : fsem abort_ = 0.
Proof. by rewrite unlock. Qed.

Lemma fsem_skipE : fsem skip_ = :1.
Proof. by rewrite unlock. Qed.

Lemma fsem_initE S v : fsem (@init_ S v) = liftfso (initialso v).
Proof. by rewrite unlock. Qed.

Lemma fsem_unitaryE S U : fsem (@unitary_ S U) = liftfso (unitaryso U).
Proof. by rewrite unlock. Qed.

Lemma fsem_ifE F S M fc : fsem (@cond_ F S M fc) = 
  ifso (liftf_fun M) (fun i : F => fsem (fc i)).
Proof. by rewrite unlock. Qed.

Lemma fsem_whileE S M b c : fsem (@while_ S M b c) = 
  whileso (liftf_fun M) b (fsem c).
Proof. by rewrite unlock. Qed.

Lemma fsem_seqE c1 c2 :
  fsem (seqc_ c1 c2) = (fsem c2) :o (fsem c1).
Proof. by rewrite unlock. Qed.

Definition fsemE := (fsem_abortE, fsem_skipE, fsem_initE, 
  fsem_unitaryE, fsem_ifE, fsem_seqE, fsem_whileE).

Lemma fsem_while_iter_ (S : {set L}) (M:'QM[H]_(bool;S)) b (c: cmd_) n :
  fsem (while_iter_ M b c n) = whileso_iter (liftf_fun M) b (fsem c) n.
Proof.
elim: n=>[|n IH/=]; first by rewrite fsemE//=.
rewrite fsem_ifE. f_equal; apply/funext=>b'.
by case: eqP; rewrite fsemE// IH.
Qed.

Lemma fsem_big I (r : seq I) (P : pred I) (F : I -> cmd_) :
  fsem (\big[seqc_/skip_]_(i <- r | P i) (F i)) =
  \compr_(i <- r | P i) fsem (F i).
Proof.
elim: r=>[|c r IH]; first by rewrite !big_nil/= fsemE.
by rewrite !big_cons; case: (P c)=>//=; rewrite fsemE comp_soElr IH.
Qed.

(* fsem returns quantum operation *)
Lemma fsem_qo (c : cmd_) : fsem c \is isqo.
Proof.
elim: c=>[||S v|S U|F S M br IH|S M b D IH|c1 IH c2 IH1]/=; rewrite fsemE.
5: have->: (fun i : F => fsem (br i)) = (fun i : F => QOType (IH i)) by [].
6,7: rewrite (qo_qoE IH) 1?(qo_qoE IH1).
all: apply/qo_isqoP.
Qed.
Canonical fsem_qoType c := QOType (fsem_qo c).
Lemma fsem_cp (c : cmd_) : fsem c \is iscp.
Proof. apply/isqo_cp/qo_isqoP. Qed.
Canonical fsem_cpType c := CPType (fsem_cp c).

(* check program contains while; if not, quantum channel *)
Fixpoint no_while (c : cmd_) :=
  match c with
  | abort_          => false
  | skip_           => true
  | init_ s v       => true
  | unitary_ _ U    => true
  | cond_ F s M fc  => \big[andb/true]_(i : F) (no_while (fc i))
  | while_ s M b c    => false
  | seqc_ c1 c2     => (no_while c1) && (no_while c2)
  end.

(* check program is pure, i.e., without initialization and if while; NS -> NS *)
Fixpoint pure_cmd (c : cmd_) :=
  match c with
  | abort_          => false
  | skip_           => true
  | init_ s v       => false
  | unitary_ _ U    => true
  | cond_ F s M fc  => false
  | while_ s M b c    => false
  | seqc_ c1 c2     => (pure_cmd c1) && (pure_cmd c2)
  end.

Lemma no_while_qc c : no_while c -> fsem c \is isqc.
Proof.
elim: c=>[|_|S v _|S U _|F S M br IH|S M b D IH|c H1 c1 H2]//=; rewrite fsemE.
4: rewrite big_andE=>/forallP/=P;
have ->: (fun i : F => fsem (br i)) = (fun i : F => QCType (IH i (P i))) by [].
5: move=>/andP[/H1 P/H2 P1]; rewrite (qc_qcE P) (qc_qcE P1).
all: apply/qc_isqcP.
Qed.

(* local denotational semantics *)
Lemma fsem_local c : exists E : 'QO[H]_(fvars c), fsem c = liftfso E.
Proof.
elim: c=>[||S v|S U|F S M br IH|S M b c [E P]|c [E P] c1 [E1 P1]]=>/=.
by exists [QO of 0]; rewrite/= fsemE linear0.
by exists [QO of :1]; rewrite/= fsemE liftfso1.
by exists [QO of initialso v]; rewrite fsemE.
by exists [QO of unitaryso U]; rewrite fsemE.
pose f i := projT1 (cid (IH i)).
have P i : fsem (br i) = liftfso (f i).
by move: (projT2 (cid (IH i))).
move: (subsetUl S (\bigcup_i fvars (br i)))=>sub.
have subi i : fvars (br i) :<=: S :|: \bigcup_i fvars (br i).
by apply/subsetU/orP; right; apply/bigcup_sup.
exists [QO of ifso (lift_fun sub M) (fun i=>liftso (subi i) (f i))]=>/=.
by rewrite fsemE liftfso_ifso liftf_fun2; f_equal; apply/funext=>i; rewrite liftfso2.
exists [QO of whileso (lift_fun (subsetUl S (fvars c)) M) b (liftso (subsetUr _ _) E)].
by rewrite fsemE liftfso_whileso/= liftf_fun2 liftfso2 P.
exists [QO of liftso (subsetUr _ _) E1 :o (liftso (subsetUl _ _) E)].
by rewrite fsemE liftfso_comp !liftfso2 P P1.
Qed.

Lemma fsem_lift (S : {set L}) c : fvars c :<=: S -> 
  exists E : 'QO[H]_S, fsem c = liftfso E.
Proof.
move=>P1; move: (fsem_local c)=>[E PE].
exists [QO of (liftso P1 E)]; by rewrite/= liftfso2.
Qed.

Lemma fsem_seqcC c1 c2 : [disjoint (fvars c1) & (fvars c2)] -> 
  fsem (seqc_ c1 c2) = fsem (seqc_ c2 c1).
Proof.
move=>dis; move: (fsem_local c1) (fsem_local c2)=>[E1 P1] [E2 P2].
by rewrite !fsemE P1 P2 -liftfso_compC.
Qed.

Lemma fsem_seqcA c1 c2 c3 : 
  fsem (seqc_ c1 (seqc_ c2 c3)) = fsem (seqc_ (seqc_ c1 c2) c3).
Proof. by rewrite !fsemE comp_soA. Qed.

End Semantics.
End QWhile.

Notation "'SKIP'" := (@skip_ _ _) : lfun_scope.
Notation "'ABORT'" := (@abort_ _ _) : lfun_scope.
Notation " c1 ';;' c2 " := (@seqc_ _ _ c1 c2) 
  (at level 74, left associativity, format "c1  ;;  c2") : lfun_scope.
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

Notation "[ 'for' i <- r | P 'do' F ]" :=
  (\big[@seqc_ _ _ /@skip_ _ _ ]_(i <- r | P%B) F%VF) : lfun_scope.
Notation "[ 'for' i <- r 'do' F ]" :=
  (\big[@seqc_ _ _ /@skip_ _ _ ]_(i <- r) F%VF) : lfun_scope.
Notation "[ 'for' m <= i < n | P 'do' F ]" :=
  (\big[@seqc_ _ _ /@skip_ _ _ ]_(m <= i < n | P%B) F%VF) : lfun_scope.
Notation "[ 'for' m <= i < n 'do' F ]" :=
  (\big[@seqc_ _ _ /@skip_ _ _ ]_(m <= i < n) F%VF) : lfun_scope.
Notation "[ 'for' i | P 'do' F ]" :=
  (\big[@seqc_ _ _ /@skip_ _ _ ]_(i | P%B) F%VF) : lfun_scope.
Notation "[ 'for' i 'do' F ]" :=
  (\big[@seqc_ _ _ /@skip_ _ _ ]_i F%VF) : lfun_scope.
Notation "[ 'for' i : t | P 'do' F ]" :=
  (\big[@seqc_ _ _ /@skip_ _ _ ]_(i : t | P%B) F%VF) (only parsing) : lfun_scope.
Notation "[ 'for' i : t 'do' F ]" :=
  (\big[@seqc_ _ _ /@skip_ _ _ ]_(i : t) F%VF) (only parsing) : lfun_scope.
Notation "[ 'for' i < n | P 'do' F ]" :=
  (\big[@seqc_ _ _ /@skip_ _ _ ]_(i < n | P%B) F%VF) : lfun_scope.
Notation "[ 'for' i < n 'do' F ]" :=
  (\big[@seqc_ _ _ /@skip_ _ _ ]_(i < n) F%VF) : lfun_scope.
Notation "[ 'for' i 'in' A | P 'do' F ]" :=
  (\big[@seqc_ _ _ /@skip_ _ _ ]_(i in A | P%B) F%VF) : lfun_scope.
Notation "[ 'for' i 'in' A 'do' F ]" :=
  (\big[@seqc_ _ _ /@skip_ _ _ ]_(i in A) F%VF) : lfun_scope.

(* Notation "x <<- e" := (@init_ _ _ x e) 
  (at level 65, e at level 70, no associativity, format "x  <<-  e") : lfun_scope. *)
(* Notation "'If' M [ F ; S ] 'then' f" := (@cond_ _ _ _ F S M f) 
  (at level 65, right associativity, format
"'If'  M [ F ; S ]  'then'  f") : lfun_scope.
Notation "'While' M [ S ] 'Do' c" := (@while_ _ _ _ S M c) 
  (at level 65, right associativity, format
"'While'  M [ S ]  'Do'  c") : lfun_scope. *)


Definition eqcmd L H (c1 c2 : @cmd_ L H) := fsem c1 = fsem c2.
Infix "=s" := eqcmd (at level 70) : lfun_scope.

Lemma eqcmd_trans L H : 
  forall (a b c: @cmd_ L H), a =s b -> b =s c -> a =s c.
Proof. by rewrite /eqcmd; move=>a b c -> ->. Qed.

Lemma eqcmd_refl L H : forall (a: @cmd_ L H), a =s a.
Proof. by []. Qed.

Lemma eqcmd_sym L H : forall (a b : @cmd_ L H), a =s b -> b =s a.
Proof. by rewrite /eqcmd; move=>a b ->. Qed.

Add Parametric Relation L H : (@cmd_ L H) (@eqcmd L H)
  reflexivity proved by (@eqcmd_refl L H)
  symmetry proved by (@eqcmd_sym L H)
  transitivity proved by (@eqcmd_trans L H)
  as eqcmd_rel.

Add Parametric Morphism L H S (M : 'QM[H]_(bool;S)) b : 
  (@while_ L H S M b)
  with signature (@eqcmd L H) ==> (@eqcmd L H) as eqcmd_while_mor.
Proof. by move=>x y; rewrite /eqcmd !fsemE=>/=->. Qed.  

Add Parametric Morphism L H : (@seqc_ L H)
  with signature (@eqcmd L H) ==> (@eqcmd L H) ==> (@eqcmd L H) as eqcmd_seqc_mor.
Proof. by rewrite /eqcmd unlock/==>x y->x' y'->. Qed.  

Section EqFsem.
Context (L : finType) (H : L -> chsType).
Local Notation cmd := (cmd_ H).

Lemma fsem_seqA (c1 c2 c3 : cmd) : (c1 ;; (c2 ;; c3)) =s (c1 ;; c2 ;; c3).
Proof. exact: fsem_seqcA. Qed.

Lemma fsem_seqC (c1 c2 : cmd) : 
  [disjoint (fvars c1) & (fvars c2)] -> (c1 ;; c2) =s (c2 ;; c1).
Proof. exact: fsem_seqcC. Qed.

Lemma fsem_eqif F S M f g :
  (forall i, f i =s g i) ->  @cond_ _ H F S M f =s (@cond_ _ H F S M g).
Proof. move=>P1; rewrite /eqcmd !fsemE; f_equal; apply/funext=> i; apply P1. Qed.

End EqFsem.

Section bindihbtype.
Context (L : finType) (H : L -> chsType).

Section Vars.

(* remark : even two vars are different, their vset might not be disjoint *)
(* to use vars, keep the disjoint assumption everywhere *)
(* a bijection mapping from T and 'Idx[H]_S should be given *)
(* this is crucial for packing variables *)
Inductive vars_r (T : ihbFinType) :=
| Var (S : {set L}) (t2i : T -> 'Idx[H]_S) 
  (bf : {i2t | cancel t2i i2t & cancel i2t t2i}).

Definition tvars_of (T : ihbFinType) (phT : phant T) := @vars_r T.
Notation vars T := (tvars_of (Phant T)).

Definition vset {T : ihbFinType} (v : vars T) :=
  let: Var t _ _ := v in t.
Definition vt2i {T : ihbFinType} (v : vars T) : T -> 'Idx[H]_(vset v) :=
  let: Var _ f _ := v in f.
Definition vt2i_bij_subproof {T : ihbFinType} (v : vars T) : 
  {i2t | cancel (vt2i v) i2t & cancel i2t (vt2i v)} :=
  let: Var _ _ bij := v in bij.

Canonical vars_eqType (T : ihbFinType) :=
  EqType (vars T) gen_eqMixin.
Canonical vars_choiceType (T : ihbFinType) :=
  ChoiceType (vars T) gen_choiceMixin.

(* Definition disvar (F : eqType) (FT : forall i : F, ihbFinType)
  (vf : forall i : F, vars (FT i)) :=
    forall i j, i != j -> [disjoint (vset (vf i)) & (vset (vf j))]. *)

End Vars.

Section VarsTheory.
Notation vars T := (tvars_of (Phant T)).
Variable (T : ihbFinType) (x : vars T).

Definition vi2t := sval (vt2i_bij_subproof x).
Lemma vt2iK : cancel (vt2i x) vi2t.
Proof. by move: (svalP (vt2i_bij_subproof x))=>[]. Qed.
Lemma vi2tK : cancel vi2t (vt2i x).
Proof. by move: (svalP (vt2i_bij_subproof x))=>[]. Qed.
Lemma vt2i_inj : injective (vt2i x).
Proof. exact: (can_inj vt2iK). Qed.
Lemma vi2tK_inj : injective vi2t.
Proof. exact: (can_inj vi2tK). Qed.
Lemma vt2i_bij : bijective (vt2i x).
Proof. exists vi2t; [exact: vt2iK | exact: vi2tK]. Qed.
Lemma vi2t_bij : bijective vi2t.
Proof. exists (vt2i x); [exact: vi2tK | exact: vt2iK]. Qed.

Lemma vset_dim : #|T| = Vector.dim 'H[H]_(vset x).
Proof. rewrite dim_ffunr; apply: (bij_eq_card vt2i_bij). Qed.

(* i --n2i--> 'Idx --vi2t--> T --enum--> 'I_#|T| --cast--> 'I_(dim 'Hs T) *)
Definition idx_tv2v (i : 'I_(Vector.dim 'Hs T)) : 'I_(Vector.dim 'H[H]_(vset x))
  := (i2n (vt2i x (enum_val (cast_ord (esym (ihb_dim_cast T)) i)))).
Definition idx_v2tv (i : 'I_(Vector.dim 'H[H]_(vset x))) : 'I_(Vector.dim 'Hs T)
  := (cast_ord (ihb_dim_cast T) (enum_rank (vi2t (n2i i)))).

Lemma idx_tv2vK : cancel idx_tv2v idx_v2tv.
Proof. by move=>i; rewrite /idx_tv2v/idx_v2tv i2nK 
vt2iK enum_valK cast_ord_comp cast_ord_id. Qed.
Lemma idx_v2tvK : cancel idx_v2tv idx_tv2v.
Proof. by move=>i; rewrite /idx_tv2v/idx_v2tv 
cast_ord_comp cast_ord_id enum_rankK vi2tK n2iK. Qed.

End VarsTheory.

Notation vars T := (tvars_of (Phant T)).
Notation "'lb' x" := (vset x) (at level 10, only parsing).
Notation "''' x" := (vset x) (at level 0, format "''' x", only printing).

(* gives the definition of packing variables *)
(* for example, x is a n.-tuple (vars bool), we can pack x together *)
(* as px, which is vars (n.tuple bool), this allows us to treat  *)
(* a collection of vars as a single var *)
(* since we explicitly give the way how to map ihbFinType to 'Idx *)
(* we are able to derive the desired properties, i.e. *)
(* packing variable is same as the tensor of their elements *)
Section pvars.
Implicit Type (T : ihbFinType).

Definition pvars2_t2i T1 T2 (x : vars T1) (y : vars T2) (t : T1 * T2) :=
  idxU (vt2i x t.1) (vt2i y t.2).
Lemma pvars2_subproof T1 T2 x y (dxy : [disjoint lb x & lb y]) :
  {i2t | cancel (@pvars2_t2i T1 T2 x y) i2t & cancel i2t (@pvars2_t2i _ _ x y)}.
Proof.
exists (fun i=> (vi2t (idxSl i), vi2t (idxSr i)))=>i;
by rewrite /pvars2_t2i/= ?idxSUl// ?idxSUr// ?vt2iK 
  ?vi2tK ?idxUS// -surjective_pairing.
Qed.
Definition pvars2 T1 T2 x y dxy : vars (T1 * T2) := 
  Var (@pvars2_subproof T1 T2 x y dxy).

Lemma pvars2_vset T1 T2 x y dis :
  lb (@pvars2 T1 T2 x y dis) = lb x :|: lb y.
Proof. by []. Qed.

Definition pvars_tuple_t2i T n (x : n.-tuple (vars T)) (t : n.-tuple T) :=
  packidx [ffun i : 'I_n => vt2i (x ~_ i) (t ~_ i)].
Lemma pvars_tuple_subproof T n (x : n.-tuple (vars T)) 
  (dis : forall i j, i != j -> [disjoint (vset (x ~_ i)) & (vset (x ~_ j))]) :
  {i2t | cancel (@pvars_tuple_t2i T n x) i2t & 
    cancel i2t (@pvars_tuple_t2i T n x)}.
Proof.
exists (fun i=> tuple_of_finfun [ffun k : 'I_n => vi2t (flatidx i k)])=>i.
by apply eq_from_tnth=>j; rewrite tnth_map tnth_ord_tuple 
  ffunE packidxK// ffunE vt2iK.
by apply/flatidx_inj/ffunP=>j; rewrite packidxK// ffunE 
  tnth_map tnth_ord_tuple ffunE vi2tK.
Qed.
Definition pvars_tuple T n x dis : vars (n.-tuple T) := 
  Var (@pvars_tuple_subproof T n x dis).

Lemma pvars_tuple_vset T n x dis :
  lb (@pvars_tuple T n x dis) = \bigcup_i (lb (x ~_ i)).
Proof. by []. Qed.

Definition pvars_dffun_t2i (F : finType) (TF : F -> ihbFinType) 
  (x : forall i : F, vars (TF i)) (t : {dffun forall i : F, TF i}) :=
  packidx [ffun i : F => vt2i (x i) (t i)].
Lemma pvars_dffun_subproof (F : finType) TF x
  (dis : forall i j, i != j -> [disjoint lb (x i) & lb (x j)]) :
  {i2t | cancel (@pvars_dffun_t2i F TF x) i2t & 
    cancel i2t (@pvars_dffun_t2i F TF x)}.
Proof.
exists (fun i=>[ffun k : F => vi2t (flatidx i k)])=>i.
by apply/ffunP=>j; rewrite ffunE packidxK// ffunE vt2iK.
by apply/flatidx_inj/ffunP=>j; rewrite packidxK// 2 !ffunE vi2tK.
Qed.
Definition pvars_dffun (F : finType) (TF : forall i : F, ihbFinType) x dis
  : vars {dffun forall i : F, TF i} := Var (@pvars_dffun_subproof F TF x dis).

Lemma pvars_dffun_vset F TF x dis :
  lb (@pvars_dffun F TF x dis) = \bigcup_i (lb (x i)).
Proof. by []. Qed.

Definition pvars_ffun (F : finType) T (x : F -> vars T) dis : vars ({ffun F -> T}) 
  := @pvars_dffun _ _ x dis.

Lemma pvars_ffun_vset F T x dis :
  lb (@pvars_ffun F T x dis) = \bigcup_i (lb (x i)).
Proof. by []. Qed.

Definition pvars_vset := (pvars2_vset, pvars_tuple_vset, 
  pvars_ffun_vset, pvars_dffun_vset).

End pvars.

Variable (T : ihbFinType) (x : vars T).

Definition tv2v (v : 'Hs T) : 'H[H]_(lb x) :=
  r2v (\row_i (v2r v) ord0 (idx_v2tv i)).
Definition v2tv (v : 'H[H]_(lb x)) : 'Hs T := 
  r2v (\row_i (v2r v) ord0 (idx_tv2v x i)).
Lemma tv2vK : cancel tv2v v2tv.
Proof. by move=>t; apply/v2r_inj/matrixP=>i j; rewrite !r2vK !mxE idx_tv2vK !ord1. Qed.
Lemma v2tvK : cancel v2tv tv2v.
Proof. by move=>t; apply/v2r_inj/matrixP=>i j; rewrite !r2vK !mxE idx_v2tvK !ord1. Qed.
Lemma tv2v_inj : injective tv2v. Proof. exact: (can_inj tv2vK). Qed.
Lemma v2tv_inj : injective v2tv. Proof. exact: (can_inj v2tvK). Qed.
Lemma tv2v_dot u v : [<tv2v u ; tv2v v >] = [<u ; v>].
Proof.
rewrite !dotp_mulmx !r2vK !mxE (reindex (idx_tv2v x)).
by exists (@idx_v2tv _ x)=>i _; rewrite ?idx_tv2vK// idx_v2tvK.
by apply eq_bigr=>i _; rewrite !mxE idx_tv2vK.
Qed.
Lemma v2tv_dot u v : [<v2tv u ; v2tv v >] = [<u ; v>].
Proof. by rewrite -{2}(v2tvK u) -{2}(v2tvK v) tv2v_dot. Qed.
Lemma tv2v_norm (u : 'Hs T) : `|tv2v u| = `|u|.
Proof. by rewrite !hnormE tv2v_dot. Qed.

Lemma v2tv_is_linear : linear v2tv.
Proof.
move=>a b c; apply/v2r_inj/matrixP=>i j.
by rewrite linearP/= !r2vK linearP/= !mxE.
Qed.
Canonical v2tv_additive := Additive v2tv_is_linear.
Canonical v2tv_linear := Linear v2tv_is_linear.
Lemma tv2v_is_linear : linear tv2v.
Proof. exact: (can2_linear v2tvK tv2vK). Qed.
Canonical tv2v_additive := Additive tv2v_is_linear.
Canonical tv2v_linear := Linear tv2v_is_linear.

Lemma tv2v_conj u : (tv2v u)^*v = tv2v u^*v.
Proof. by apply/v2r_inj/matrixP=>i j; rewrite !r2vK !mxE. Qed.  

Definition tf2f (f : 'End[T]) : 'F[H]_(lb x) := 
  Vector.Hom (\matrix_(i,j) (f2mx f) (idx_v2tv i) (idx_v2tv j)).
Definition f2tf (f : 'F[H]_(lb x)) : 'End[T] :=
  Vector.Hom (\matrix_(i,j) (f2mx f) (idx_tv2v x i) (idx_tv2v x j)).
Lemma tf2fK : cancel tf2f f2tf.
Proof. by move=>t; apply/f2mx_inj/matrixP=>i j; rewrite/= !mxE !idx_tv2vK. Qed.
Lemma f2tfK : cancel f2tf tf2f.
Proof. by move=>t; apply/f2mx_inj/matrixP=>i j; rewrite/= !mxE !idx_v2tvK. Qed.
Lemma tf2f_inj : injective tf2f. Proof. exact: (can_inj tf2fK). Qed.
Lemma f2tf_inj : injective f2tf. Proof. exact: (can_inj f2tfK). Qed.
Lemma f2tf_is_linear : linear f2tf.
Proof.
move=>a b c; apply/f2mx_inj/matrixP=>i j.
by rewrite linearP/= mxE linearP/= !mxE.
Qed.
Canonical f2tf_additive := Additive f2tf_is_linear.
Canonical f2tf_linear := Linear f2tf_is_linear.
Lemma tf2f_is_linear : linear tf2f.
Proof. exact: (can2_linear f2tfK tf2fK). Qed.
Canonical tf2f_additive := Additive tf2f_is_linear.
Canonical tf2f_linear := Linear tf2f_is_linear.

Lemma tf2fD (f g : 'End[T]) : (tf2f f) + (tf2f g) = tf2f (f + g).
Proof. by rewrite linearD. Qed.
Lemma tf2fN (f : 'End[T]) : - (tf2f f) = tf2f (- f).
Proof. by rewrite linearN. Qed.
Lemma tf2fZ (c : C) (f : 'End[T]) : c *: (tf2f f) = tf2f (c *: f).
Proof. by rewrite linearZ. Qed.
Lemma tf2fB (f g : 'End[T]) : (tf2f f) - (tf2f g) = tf2f (f - g).
Proof. by rewrite linearB. Qed.
Lemma tf2f_comp (f g : 'End[T]) : (tf2f f) \o (tf2f g) = tf2f (f \o g).
Proof.
apply/f2mx_inj/matrixP=>i j; rewrite !(f2mx_comp, mxE)/= (reindex (idx_tv2v x)).
by exists (@idx_v2tv _ x)=>k _; rewrite ?idx_tv2vK// idx_v2tvK.
by apply eq_bigr=>k _; rewrite !mxE idx_tv2vK.
Qed.
Lemma tf2f_adj (f : 'End[T]) : (tf2f f)^A = tf2f (f^A).
Proof. by apply/f2mx_inj/matrixP=>i j; rewrite !mxE. Qed.
Lemma tf2f_tr (f : 'End[T]) : (tf2f f)^T = tf2f f^T.
Proof. by apply/f2mx_inj/matrixP=>i j; rewrite !mxE. Qed.
Lemma tf2f_conj (f : 'End[T]) : (tf2f f)^C = tf2f f^C.
Proof. by rewrite !conjfAT tf2f_adj tf2f_tr. Qed.
Lemma tf2f_apply (f : 'End[T]) (v : 'Hs T) :
  (tf2f f) (tv2v v) = tv2v (f v).
Proof.
apply/v2r_inj/matrixP=>i j; rewrite/= unlock/= !r2vK !mxE (reindex (idx_tv2v x)).
by exists (@idx_v2tv _ x)=>k _; rewrite ?idx_tv2vK// idx_v2tvK.
by apply eq_bigr=>k _; rewrite !mxE idx_tv2vK.
Qed.
Lemma tf2f_trlf (f : 'End[T]) : \Tr (tf2f f) = \Tr f.
Proof.
rewrite/lftrace/=/mxtrace (reindex (idx_tv2v x)).
by exists (@idx_v2tv _ x)=>k _; rewrite ?idx_tv2vK// idx_v2tvK.
by apply eq_bigr=>k _; rewrite !mxE idx_tv2vK.
Qed.
Lemma tv2vD (f g : 'Hs T) : (tv2v f) + (tv2v g) = tv2v (f + g).
Proof. by rewrite linearD. Qed.
Lemma tv2vB (f g : 'Hs T) : (tv2v f) - (tv2v g) = tv2v (f - g).
Proof. by rewrite linearB. Qed.
Lemma tv2vN (f : 'Hs T) : - (tv2v f) = tv2v (- f).
Proof. by rewrite linearN. Qed.
Lemma tv2vZ (c : C) (f : 'Hs T) : c *: (tv2v f) = tv2v (c *: f).
Proof. by rewrite linearZ. Qed.
Lemma tv2v_out (u v : 'Hs T) : 
  [> tv2v u ; tv2v v <] = tf2f [> u ; v <].
Proof. by apply/lfunP=>w; rewrite -(v2tvK w) outpE tv2v_dot tf2f_apply outpE linearZ. Qed.

Lemma tf2f1 : \1 = tf2f \1.
Proof. by apply/lfunP=>v; rewrite lfunE/= -{2}(v2tvK v) tf2f_apply lfunE/= v2tvK. Qed.
Lemma tf2f0 : 0 = tf2f 0. Proof. by rewrite linear0. Qed.
Lemma tv2v0 : 0 = tv2v 0. Proof. by rewrite linear0. Qed.

Definition f2tfE := (tf2fD, tf2fN, tf2fZ, tf2f_comp, tf2f_adj, 
tf2f_tr, tf2f_conj, tf2f_apply, tv2vD, tv2vN, tv2vZ, tf2f1, 
tf2f0, tv2v0,tv2v_dot,tv2v_out).

(* canonical structures of tv2v v2tv tf2f f2tf *)
(* NS psd den obs unitary den1 proj proj1 *)
Lemma tv2v_ns (v : 'NS(_)) : [< tv2v v ; tv2v v >] == 1.
Proof. by rewrite tv2v_dot ns_dot. Qed.
Canonical tv2v_nsType v := NSType (@tv2v_ns v).
Lemma v2tv_ns (v : 'NS(_)) : [< v2tv v ; v2tv v >] == 1.
Proof. by rewrite v2tv_dot ns_dot. Qed.
Canonical v2tv_nsType v := NSType (@v2tv_ns v).
Definition tv2v_fun (F : finType) (f : F -> 'Hs T) i := tv2v (f i).
Lemma tv2v_funE (F : finType) (f : F -> 'Hs T) i : tv2v_fun f i = tv2v (f i).
Proof. by []. Qed.
Lemma tv2v_ponb_dot (F : finType) (f : 'PONB(F;'Hs T)) i j :
  [< tv2v_fun f i; tv2v_fun f j >] = (i == j)%:R.
Proof. by rewrite tv2v_dot ponb_dot. Qed.
Lemma tv2v_onb_dot (F : finType) (f : 'ONB(F;'Hs T)) i j :
  [< tv2v_fun f i; tv2v_fun f j >] = (i == j)%:R.
Proof. exact: tv2v_ponb_dot. Qed.
Lemma tv2v_onb_dim (F : finType) (f : 'ONB(F;'Hs T)) :
  #|F| = Vector.dim ('H[H]_(lb x)).
Proof. by rewrite (onb_card f) -(vset_dim x) -ihb_dim_cast/=. Qed.
Canonical tv2v_ponbasis F f := PONBasis (@tv2v_ponb_dot F f).
Canonical tv2v_onbasis F f := ONBasis (@tv2v_onb_dot F f) (@tv2v_onb_dim F f).

(* move *)
Lemma unitarylfE (U : chsType) (A : 'End(U)) : (A \is unitarylf) = (A^A \o A == \1).
Proof. by apply/eqb_iff; rewrite eq_iff; split=>/unitarylfP. Qed.

Lemma tf2f_hermE f : tf2f f \is hermlf = (f \is hermlf).
Proof. by rewrite !hermlfE tf2f_adj (inj_eq tf2f_inj). Qed.
Lemma tf2f_psdE f : tf2f f \is psdlf = (f \is psdlf).
Proof.
apply/eqb_iff; split=>/psdlfP P; apply/psdlfP=>v.
by move: (P (tv2v v)); rewrite tf2f_apply tv2v_dot.
by rewrite -(v2tvK v) tf2f_apply tv2v_dot.
Qed.
Lemma tf2f_denE f : tf2f f \is denlf = (f \is denlf).
Proof.
apply/eqb_iff; split=>/denlfP P; apply/denlfP; move: P;
by rewrite tf2f_psdE tf2f_trlf.
Qed.
Lemma tf2f_obsE f : tf2f f \is obslf = (f \is obslf).
Proof.
apply/eqb_iff; split=>/obslfP P; apply/obslfP; move: P;
rewrite tf2f_psdE=>[[P1 P2]]; split=>// u.
by move: (P2 (tv2v u)); rewrite tf2f_apply !tv2v_dot.
by rewrite -(v2tvK u); rewrite tf2f_apply !tv2v_dot.
Qed.
Lemma tf2f_unitaryE f : tf2f f \is unitarylf = (f \is unitarylf).
Proof. by rewrite !unitarylfE tf2f_adj tf2f_comp -(inj_eq tf2f_inj) -tf2f1. Qed.
Lemma tf2f_den1E f : tf2f f \is den1lf = (f \is den1lf).
Proof.
apply/eqb_iff; split=>/den1lfP P; apply/den1lfP; move: P;
by rewrite tf2f_psdE tf2f_trlf.
Qed.
Lemma tf2f_projE f : tf2f f \is projlf = (f \is projlf).
Proof.
apply/eqb_iff; split=>/projlfP P; apply/projlfP; move: P;
rewrite tf2f_adj tf2f_comp; last by move=>[]->->.
by move=>[]/tf2f_inj->/tf2f_inj->.
Qed.
Lemma tf2f_proj1E f : tf2f f \is proj1lf = (f \is proj1lf).
Proof.
apply/eqb_iff; split=>/proj1lfP P; apply/proj1lfP; move: P;
by rewrite tf2f_projE tf2f_trlf.
Qed.
Lemma f2tf_hermE f : f2tf f \is hermlf = (f \is hermlf).
Proof. by rewrite -tf2f_hermE f2tfK. Qed.
Lemma f2tf_psdE f : f2tf f \is psdlf = (f \is psdlf).
Proof. by rewrite -tf2f_psdE f2tfK. Qed.
Lemma f2tf_denE f : f2tf f \is denlf = (f \is denlf).
Proof. by rewrite -tf2f_denE f2tfK. Qed.
Lemma f2tf_obsE f : f2tf f \is obslf = (f \is obslf).
Proof. by rewrite -tf2f_obsE f2tfK. Qed.
Lemma f2tf_unitaryE f : f2tf f \is unitarylf = (f \is unitarylf).
Proof. by rewrite -tf2f_unitaryE f2tfK. Qed.
Lemma f2tf_den1E f : f2tf f \is den1lf = (f \is den1lf).
Proof. by rewrite -tf2f_den1E f2tfK. Qed.
Lemma f2tf_projE f : f2tf f \is projlf = (f \is projlf).
Proof. by rewrite -tf2f_projE f2tfK. Qed.
Lemma f2tf_proj1E f : f2tf f \is proj1lf = (f \is proj1lf).
Proof. by rewrite -tf2f_proj1E f2tfK. Qed.

Lemma tf2f_herm (f : 'FH(_)) : tf2f f \is hermlf. Proof. by rewrite tf2f_hermE hermf_herm. Qed.
Lemma f2tf_herm (f : 'FH(_)) : f2tf f \is hermlf. Proof. by rewrite f2tf_hermE hermf_herm. Qed.
Canonical tf2f_hermfType f := HermfType (@tf2f_herm f).
Canonical f2tf_hermfType f := HermfType (@f2tf_herm f).
Lemma tf2f_psd (f : 'F+(_)) : tf2f f \is psdlf. Proof. by rewrite tf2f_psdE psdf_psd. Qed.
Lemma f2tf_psd (f : 'F+(_)) : f2tf f \is psdlf. Proof. by rewrite f2tf_psdE psdf_psd. Qed.
Canonical tf2f_psdfType f := PsdfType (@tf2f_psd f).
Canonical f2tf_psdfType f := PsdfType (@f2tf_psd f).
Lemma tf2f_den (f : 'FD(_)) : tf2f f \is denlf. Proof. by rewrite tf2f_denE denf_den. Qed.
Lemma f2tf_den (f : 'FD(_)) : f2tf f \is denlf. Proof. by rewrite f2tf_denE denf_den. Qed.
Canonical tf2f_denfType f := DenfType (@tf2f_den f).
Canonical f2tf_denfType f := DenfType (@f2tf_den f).
Lemma tf2f_obs (f : 'FO(_)) : tf2f f \is obslf. Proof. by rewrite tf2f_obsE obsf_obs. Qed.
Lemma f2tf_obs (f : 'FO(_)) : f2tf f \is obslf. Proof. by rewrite f2tf_obsE obsf_obs. Qed.
Canonical tf2f_obsfType f := ObsfType (@tf2f_obs f).
Canonical f2tf_obsfType f := ObsfType (@f2tf_obs f).
Lemma tf2f_unitary (f : 'FU(_)) : tf2f f \is unitarylf. Proof. by rewrite tf2f_unitaryE unitaryf_unitary. Qed.
Lemma f2tf_unitary (f : 'FU(_)) : f2tf f \is unitarylf. Proof. by rewrite f2tf_unitaryE unitaryf_unitary. Qed.
Canonical tf2f_unitaryfType f := UnitaryfType (@tf2f_unitary f).
Canonical f2tf_unitaryfType f := UnitaryfType (@f2tf_unitary f).
Lemma tf2f_den1 (f : 'FD1(_)) : tf2f f \is den1lf. Proof. by rewrite tf2f_den1E den1f_den1. Qed.
Lemma f2tf_den1 (f : 'FD1(_)) : f2tf f \is den1lf. Proof. by rewrite f2tf_den1E den1f_den1. Qed.
Canonical tf2f_den1fType f := Den1fType (@tf2f_den1 f).
Canonical f2tf_den1fType f := Den1fType (@f2tf_den1 f).
Lemma tf2f_proj (f : 'FP(_)) : tf2f f \is projlf. Proof. by rewrite tf2f_projE projf_proj. Qed.
Lemma f2tf_proj (f : 'FP(_)) : f2tf f \is projlf. Proof. by rewrite f2tf_projE projf_proj. Qed.
Canonical tf2f_projfType f := ProjfType (@tf2f_proj f).
Canonical f2tf_projfType f := ProjfType (@f2tf_proj f).
Lemma tf2f_proj1 (f : 'FP1(_)) : tf2f f \is proj1lf. Proof. by rewrite tf2f_proj1E proj1f_proj1. Qed.
Lemma f2tf_proj1 (f : 'FP1(_)) : f2tf f \is proj1lf. Proof. by rewrite f2tf_proj1E proj1f_proj1. Qed.
Canonical tf2f_proj1fType f := Proj1fType (@tf2f_proj1 f).
Canonical f2tf_proj1fType f := Proj1fType (@f2tf_proj1 f).

Definition t2vx (tx : T) := tv2v (t2tv tx).
Lemma t2vx_dot (tx1 tx2 : T) : [< t2vx tx1; t2vx tx2>] = (tx1 == tx2)%:R.
Proof. by rewrite tv2v_dot t2tv_dot. Qed.
Lemma t2vx_ns tx : [<t2vx tx ; t2vx tx >] == 1.
Proof. by rewrite t2vx_dot eqxx. Qed.
Canonical t2vx_nsType tx := Eval hnf in [NS of t2vx tx].
Canonical t2vx_ponbasis := Eval hnf in [PONB of t2vx as (tv2v_fun (@t2tv T))].
Canonical t2vx_onbasis := Eval hnf in [ONB of t2vx as (tv2v_fun (@t2tv T))].
Lemma t2vx_conj tx : (t2vx tx)^*v = t2vx tx.
Proof. by rewrite /t2vx tv2v_conj t2tv_conj. Qed.

(* tf2f and f2tf : lef, ltf, le1, ge0 *)
Lemma tf2f_lef (u v : 'End[T]) : tf2f u ⊑ tf2f v = (u ⊑ v).
Proof.
apply/Bool.eq_iff_eq_true; split=>/lef_dot P;
apply/lef_dot=>f. move: (P (tv2v f)). 2: rewrite -(v2tvK f).
all: by rewrite !tf2f_apply !tv2v_dot.
Qed.
Lemma tf2f_ltf (u v : 'End[T]) : tf2f u ⊏ tf2f v = (u ⊏ v).
Proof. by rewrite !lt_def tf2f_lef (can_eq tf2fK). Qed.
Lemma tf2f_le1 (u : 'End[T]) : tf2f u ⊑ \1 = (u ⊑ \1).
Proof. by rewrite tf2f1 tf2f_lef. Qed.
Lemma tf2f_ge0 (u : 'End[T]) : (0 : 'End(_)) ⊑ tf2f u = ((0 : 'End(_)) ⊑ u).
Proof. by rewrite tf2f0 tf2f_lef. Qed.

Lemma f2tf_lef (u v : 'F[H]_(lb x)) : f2tf u ⊑ f2tf v = (u ⊑ v).
Proof. by rewrite -tf2f_lef !f2tfK. Qed.
Lemma f2tf_ltf (u v : 'F[H]_(lb x)) : f2tf u ⊏ f2tf v = (u ⊏ v).
Proof. by rewrite -tf2f_ltf !f2tfK. Qed.

(* inject measurement *)
Definition tm2m (F : finType) (f : F -> 'End[T]) := (fun i : F => tf2f (f i)).
Lemma tm2m_tn (F : finType) (f : 'TN(F;'Hs T)) : trace_nincr (tm2m f).
Proof.
rewrite /trace_nincr /tm2m.
under eq_bigr do rewrite tf2f_adj tf2f_comp.
rewrite -linear_sum/= tf2f_le1; apply/tn_tnP.
Qed.
Canonical tm2m_tnType F f := TNType (@tm2m_tn F f).
Lemma tm2m_tp (F : finType) (f : 'QM(F;'Hs T)) : trace_presv (tm2m f).
Proof.
rewrite /trace_presv /tm2m.
under eq_bigr do rewrite tf2f_adj tf2f_comp.
by rewrite -linear_sum/= qm_tpE tf2f1.
Qed.
Canonical tm2m_qmType F f := QMType (@tm2m_tp F f).

Lemma tm2mE (F : finType) (f : F -> 'End[T]) i : tm2m f i = tf2f (f i).
Proof. by []. Qed.

End bindihbtype.
(* redefine following vars when L H are provide
Notation vars T := (@tvars_of L H _ (Phant T)). *)
Notation "'lb' x" := (vset x) (at level 10, only parsing).
Notation "''' x" := (vset x) (at level 0, format "''' x", only printing).
Notation "'''' b" := (t2tv b) (at level 2, format "'''' b").

(* tv2v/tf2f (pvars x) (tentv/tentf_ffun f) = tenvm/tenfm (tv2v/tf2f (x i) (f i))*)
Section PackingCorrect.
Context (L : finType) (H : L -> chsType).
Notation vars T := (@tvars_of L H _ (Phant T)).
Implicit Type (T : ihbFinType).

Lemma tv2v_delta T (x : vars T) (t : T) :
  tv2v x ''t = deltav (vt2i x t).
Proof.
apply/v2r_inj/matrixP=>i j; rewrite /tv2v r2vK mxE/t2tv/mv2tv r2vK mxE.
rewrite/deltav/eb r2vK mxE ord1 eqxx/= /idx_v2tv cast_ord_comp.
by rewrite cast_ord_id enum_rankK (can2_eq (@vi2tK _ _ _ x) (@vt2iK _ _ _ x))
(can2_eq (@n2iK _ _ _) (@i2nK _ _ _)).
Qed.

Lemma pvars2_t2tv T1 T2 (x : vars T1) (y : vars T2)
  (dis : [disjoint lb x & lb y]) (t : T1 * T2) :
  (tv2v (pvars2 dis) ''t) = (tv2v x ''(t.1)) ⊗v (tv2v y ''(t.2)).
Proof.
apply/cdvP=>i; rewrite cdvt !tv2v_delta !cdvdelta/=/pvars2_t2i.
case: eqP; first by move=>->; rewrite idxSUl// idxSUr// !eqxx mulr1.
do 2 (case: eqP; rewrite ?(mul0r,mulr0)//).
move=><-<-; rewrite idxUS//.
Qed.

Lemma pvars2_tentv T1 T2 (x : vars T1) (y : vars T2)
  (dis : [disjoint lb x & lb y]) (u : 'Hs T1) (v : 'Hs T2) :
  (tv2v (pvars2 dis) (u ⊗t v)) = (tv2v x u) ⊗v (tv2v y v).
Proof.
apply/(intro_onbl (tv2v_onbasis (pvars2 dis) t2tv2_onbasis))=>[[i j]].
rewrite/=/tv2v_fun/tentv_fun/= {2}tentv_t2tv pvars2_t2tv/= tenv_dot// !tv2v_dot.
by rewrite (tv2v_dot (pvars2 dis)) tentv_dot.
Qed.

Lemma pvars_tuple_t2tv (T : ihbFinType) (n : nat) (x : n.-tuple (vars T))
  (dis : forall i j, i != j -> [disjoint lb (x ~_ i) & lb (x ~_ j)]) (t : n.-tuple T) :
  (tv2v (pvars_tuple dis) ''t) = 
  tenvm (fun i=>tv2v (x ~_ i) ''(t ~_ i)).
Proof.
pose tt := packidx [ffun i: 'I_n=> vt2i (x ~_ i) (t ~_ i) ].
transitivity (tenvm (fun i=>deltav (flatidx tt i))); last first.
by apply/tenvmP=>i; rewrite tv2v_delta/tt packidxK// ffunE.
by rewrite tv2v_delta/=/pvars_tuple_t2i -tenvmdv.
Qed.

Lemma pvars_tuple_tentv (T : ihbFinType) (n : nat) (x : n.-tuple (vars T))
  (dis : forall i j, i != j -> [disjoint lb (x ~_ i) & lb (x ~_ j)]) (v : n.-tuple 'Hs T) :
  (tv2v (pvars_tuple dis) (tentv_tuple v)) = 
  tenvm (fun i=>tv2v (x ~_ i) (v ~_ i)).
Proof.
apply/(intro_onbl (tv2v_onbasis (pvars_tuple dis) t2tv_onbasis))=>i.
rewrite/=/tv2v_fun {2}pvars_tuple_t2tv (tv2v_dot (pvars_tuple dis)).
rewrite tenvm_dot// t2tv_tuple tentv_tuple_dot.
by apply eq_bigr=>j _; rewrite tnth_ffun_tuple ffunE tv2v_dot.
Qed.

Lemma pvars_dffun_t2tv (F : finType) (TF : F -> ihbFinType) 
  (x : forall i : F, vars (TF i)) 
  (dis : forall i j, i != j -> [disjoint lb (x i) & lb (x j)])
  (t : {dffun forall i : F, TF i}) :
  (tv2v (pvars_dffun dis) ''t) = 
  tenvm (fun i=>tv2v (x i) ''(t i)).
Proof.
pose tt := packidx [ffun i: F => vt2i (x i) (t i) ].
transitivity (tenvm (fun i=>deltav (flatidx tt i))); last first.
by apply/tenvmP=>i; rewrite tv2v_delta/tt packidxK// ffunE.
by rewrite tv2v_delta/=/pvars_tuple_t2i -tenvmdv.
Qed.

Lemma pvars_dffun_tentv (F : finType) (TF : F -> ihbFinType) 
  (x : forall i : F, vars (TF i)) 
  (dis : forall i j, i != j -> [disjoint lb (x i) & lb (x j)])
  (v : forall i : F, 'Hs (TF i)) :
  (tv2v (pvars_dffun dis) (tentv_dffun v)) = 
  tenvm (fun i=>tv2v (x i) (v i)).
Proof.
apply/(intro_onbl (tv2v_onbasis (pvars_dffun dis) t2tv_onbasis))=>i.
rewrite/=/tv2v_fun {2}pvars_dffun_t2tv (tv2v_dot (pvars_dffun dis)).
rewrite tenvm_dot// t2tv_dffun tentv_dffun_dot.
by apply eq_bigr=>j _; rewrite tv2v_dot.
Qed.

Lemma pvars_ffun_t2tv (F : finType) (T : ihbFinType) (x : F -> vars T) 
  (dis : forall i j, i != j -> [disjoint lb (x i) & lb (x j)])
  (t : {ffun F -> T}) :
  (tv2v (pvars_ffun dis) ''t) = 
  tenvm (fun i=>tv2v (x i) ''(t i)).
Proof. exact: pvars_dffun_t2tv. Qed.

Lemma pvars_ffun_tentv (F : finType) (T : ihbFinType) (x : F -> vars T) 
  (dis : forall i j, i != j -> [disjoint lb (x i) & lb (x j)])
  (v : F -> 'Hs T) :
  (tv2v (pvars_ffun dis) (tentv_ffun v)) = 
  tenvm (fun i=>tv2v (x i) (v i)).
Proof. exact: pvars_dffun_tentv. Qed.

Lemma pvars2_tentf T1 T2 (x : vars T1) (y : vars T2)
  (dis : [disjoint lb x & lb y]) (u : 'End[T1]) (v : 'End[T2]) :
  (tf2f (pvars2 dis) (u ⊗f v)) = (tf2f x u) \⊗ (tf2f y v).
Proof.
apply/(intro_onb (tv2v_onbasis (pvars2 dis) t2tv2_onbasis))=>[[i j]].
rewrite/=/tv2v_fun/tentv_fun/= (tf2f_apply (pvars2 dis)) tentf_apply !pvars2_tentv.
by rewrite tenf_apply// !tf2f_apply.
Qed.

Lemma pvars_tuple_tentf (T : ihbFinType) (n : nat) (x : n.-tuple (vars T))
  (dis : forall i j, i != j -> [disjoint lb (x ~_ i) & lb (x ~_ j)]) (v : n.-tuple 'End[T]) :
  (tf2f (pvars_tuple dis) (tentf_tuple v)) = 
  tenfm (fun i=>tf2f (x ~_ i) (v ~_ i)).
Proof.
apply/(intro_onb (tv2v_onbasis (pvars_tuple dis) t2tv_onbasis))=>i.
rewrite/=/tv2v_fun (tf2f_apply (pvars_tuple dis)) t2tv_tuple tentf_tuple_apply 
  !pvars_tuple_tentv tenfm_apply//.
by apply tenvmP => j; rewrite !tnth_ffun_tuple ffunE tnth_ffun_tuple ffunE tf2f_apply.
Qed.

Lemma pvars_dffun_tentf (F : finType) (TF : F -> ihbFinType) 
  (x : forall i : F, vars (TF i)) 
  (dis : forall i j, i != j -> [disjoint lb (x i) & lb (x j)])
  (v : forall i : F, 'End[TF i]) :
  (tf2f (pvars_dffun dis) (tentf_dffun v)) = 
  tenfm (fun i=>tf2f (x i) (v i)).
Proof.
apply/(intro_onb (tv2v_onbasis (pvars_dffun dis) t2tv_onbasis))=>i.
rewrite/=/tv2v_fun (tf2f_apply (pvars_dffun dis)) t2tv_dffun tentf_dffun_apply 
  !pvars_dffun_tentv tenfm_apply//.
by apply tenvmP => j; rewrite tf2f_apply.
Qed.

Lemma pvars_ffun_tentf (F : finType) (T : ihbFinType) (x : F -> vars T) 
  (dis : forall i j, i != j -> [disjoint lb (x i) & lb (x j)])
  (v : F -> 'End[T]) :
  (tf2f (pvars_ffun dis) (tentf_ffun v)) = 
  tenfm (fun i=>tf2f (x i) (v i)).
Proof. exact: pvars_dffun_tentf. Qed.

Definition pvars_t2tv := (pvars2_t2tv, pvars_tuple_t2tv, pvars_ffun_t2tv, pvars_dffun_t2tv).
Definition pvars_tentv := (pvars2_tentv, pvars_tuple_tentv, pvars_ffun_tentv, pvars_dffun_tentv).
Definition pvars_tentf := (pvars2_tentf, pvars_tuple_tentf, pvars_ffun_tentf, pvars_dffun_tentf). 

End PackingCorrect.


Section VarsBuild.

Section BasicBuilder.
Variable (L : finType) (tidT : L -> ihbFinType).
Let HAT := (fun i : L => 'Hs (tidT i)).
Let idx_type_cast (x : L) : #|tidT x| = #|[finType of 'Idx[HAT]_[set x]]|.
Proof. by rewrite -dim_ffunr dim_setten big_set1 ihb_dim_cast. Qed.
Let t2i_type (x : L) (t : tidT x) : 'Idx[HAT]_[set x] :=
  enum_val (cast_ord (idx_type_cast x) (enum_rank t)).
Let t2i_bij (x : L) : {i2t | cancel (@t2i_type x) i2t & cancel i2t (@t2i_type x)}.
Proof.
exists (fun i=>enum_val (cast_ord (esym (idx_type_cast x)) (enum_rank i)))=>i;
by rewrite /t2i_type enum_valK cast_ord_comp cast_ord_id enum_rankK.
Qed.
Definition vars_build (x : L) := Var (t2i_bij x).
End BasicBuilder.

Section VarsTuple.
Variable (T : ihbFinType) (n : nat).
Let tidT (i : 'I_n) := T.
Let vx (i : 'I_n) : vars_r _ T := vars_build tidT i.
Let vtuple := tuple_of_finfun [ffun i=>vx i].
Lemma vtuple_build i j : i != j -> [disjoint lb (vtuple ~_ i) & lb (vtuple ~_ j)].
Proof. by rewrite !tnth_ffun_tuple !ffunE /vset/= disjoints1 inE. Qed.
(* Definition vtuple_build := pvars_tuple vtuple_dis. *)
End VarsTuple.

Section VarsDffun.
Variable (F : finType) (TF : F -> ihbFinType).
Let vfun (i : F) : vars_r _ (TF i) := vars_build TF i.
Lemma vdffun_build i j : i != j -> [disjoint lb (vfun i) & lb (vfun j)].
Proof. by rewrite /vset/= disjoints1 inE. Qed.
(* Definition vdffun_build := pvars_dffun vfun_dis. *)
End VarsDffun.

Section VarsFfun.
Variable (F : finType) (T : ihbFinType).
Let vfun (i : F) : vars_r _ T := vars_build (fun i : F => T) i.
Lemma vffun_build i j : i != j -> [disjoint lb (vfun i) & lb (vfun j)].
Proof. exact: vdffun_build. Qed.
(* Definition vffun_build := pvars_ffun vfun_dis. *)
End VarsFfun.

End VarsBuild.

Arguments vtuple_build : clear implicits.
Arguments vdffun_build [F] TF.
Arguments vffun_build : clear implicits.

Section DisjointTuple.
Context (L : finType) (H : L -> chsType).
Notation vars T := (@tvars_of L H _ (Phant T)).

Lemma rcons_disjointx (T : ihbFinType) (x sl : vars T) n (sh : n.-tuple (vars T)) : 
  (forall i : 'I_n.+1, [disjoint lb x & lb ([tuple of rcons sh sl] ~_ i)])
  <-> [disjoint lb x & lb sl] /\ (forall i, [disjoint lb x & lb (sh ~_ i)]).
Proof.
split=>[H1|[]P1 P2 i]. split=>[|i]. by move: (H1 ord_max); rewrite tnthN.
by move: (H1 (widen_ord (leqnSn n) i)); rewrite tnthNS.
by case/widenP: i=>[|i]; rewrite ?tnthN// tnthNS.
Qed.

Lemma rcons_disjoint (T : ihbFinType) (sl : vars T) n (sh : n.-tuple (vars T)) : 
  (forall i j, i != j -> [disjoint lb ([tuple of rcons sh sl] ~_ i) & 
      lb ([tuple of rcons sh sl] ~_ j)])
  <-> (forall i, [disjoint lb sl & lb (sh ~_ i)]) /\ 
      (forall i j, i != j -> [disjoint lb (sh ~_ i) & lb (sh ~_ j)]).
Proof.
split=>[H1|[]P1 P2 i j]. split=>[i|i j]. 
by move: (H1 _ _ (widen_ord_neq i)); rewrite tnthN tnthNS disjoint_sym.
by rewrite -(inj_eq widen_ord_inj)=>/H1; rewrite !tnthNS.
case/widenP: i=>[|i]; case/widenP: j=>[|j]; first by rewrite eqxx.
1,2: move=>_; rewrite tnthN tnthNS// disjoint_sym//.
by rewrite (inj_eq widen_ord_inj)=>/P2; rewrite !tnthNS.
Qed.

Lemma cons_disjointx (T : ihbFinType) (x sh : vars T) n (sl : n.-tuple (vars T)) : 
  (forall i : 'I_n.+1, [disjoint lb x & lb ([tuple of sh :: sl] ~_ i)])
  <-> [disjoint lb x & lb sh] /\ (forall i, [disjoint lb x & lb (sl ~_ i)]).
Proof.
split=>[H1|[]P1 P2 i]. split=>[|i]. by move: (H1 ord0); rewrite tnth0.
by move: (H1 (fintype.lift ord0 i)); rewrite tnthS.
by case/lift0P : i=>[|i]; rewrite ?tnth0// tnthS.
Qed.

Lemma cons_disjoint (T : ihbFinType) (sh : vars T) n (sl : n.-tuple (vars T)) : 
  (forall i j, i != j -> [disjoint lb ([tuple of sh :: sl] ~_ i) & 
      lb ([tuple of sh :: sl] ~_ j)])
  <-> (forall i, [disjoint lb sh & lb (sl ~_ i)]) /\ 
      (forall i j, i != j -> [disjoint lb (sl ~_ i) & lb (sl ~_ j)]).
Proof.
split=>[H1|[]P1 P2 i j]. split=>[i|i j]. 
by move: (H1 _ _ (neq_lift ord0 i)); rewrite tnth0 tnthS disjoint_sym.
by rewrite -(inj_eq (@lift_inj _ ord0))=>/H1; rewrite !tnthS.
case/lift0P: i=>[|i]; case/lift0P: j=>[|j]. by rewrite eqxx.
1,2: move=>_; rewrite tnth0 tnthS// disjoint_sym//.
by rewrite (inj_eq lift_inj)=>/P2; rewrite !tnthS.
Qed.
End DisjointTuple.

(* move *)
Lemma big_setU (R : Type) (idx : R) (aop : Monoid.com_law idx) (I : finType) 
  (A B : {set I}) (F : I -> R) :
  [disjoint A & B] ->
  \big[aop/idx]_(i in A :|: B) F i =
     aop (\big[aop/idx]_(i in A) F i)
         (\big[aop/idx]_(i in B) F i).
Proof.
move=>dis. move: dis {+}dis; rewrite -{1}setI_eq0=>/eqP P1 /setDidPl P2.
by rewrite (big_setID B) setIUl setIid setDUl setDv setU0 P1 P2 set0U Monoid.mulmC.
Qed.

(* for simple use, we provide the interface for two systems *)
(* i.e., x : vars T1, y : vars T2, apply U : 'End[T1 * T2] to x y directly *)
(* without first packing pvars2 x y. they are indeed equivalent *)
Section Inject.
Context (L : finType) (H : L -> chsType).
Notation vars T := (@tvars_of L H _ (Phant T)).
Implicit Type (T : ihbFinType).

Section Inject.
Variable (T1 T2 : ihbFinType) (x : vars T1) (y : vars T2).
Implicit Type (dis : [disjoint lb x & lb y]).

(* two qudits injection *)
Fact tv2v2_key : unit. Proof. by []. Qed.
Definition tv2v2 (v : 'Hs (T1 * T2)) : 'H[H]_(lb x :|: lb y) :=
  locked_with tv2v2_key (\sum_i [<''(i.1) ⊗t ''(i.2) ; v>] *: (tv2v x ''(i.1) ⊗v tv2v y ''(i.2))).
Canonical tv2v2_unlockable v := [unlockable of tv2v2 v].
Fact v2tv2_key : unit. Proof. by []. Qed.
Definition v2tv2 (v : 'H[H]_(lb x :|: lb y)) : 'Hs (T1 * T2) :=
  locked_with v2tv2_key (\sum_i [<tv2v x ''(i.1) ⊗v tv2v y ''(i.2) ; v>] *: (''(i.1) ⊗t ''(i.2))).
Canonical v2tv2_unlockable v := [unlockable of v2tv2 v].

Lemma tv2v2E v : tv2v2 v =
  \sum_i [<''(i.1) ⊗t ''(i.2) ; v>] *: (tv2v x ''(i.1) ⊗v tv2v y ''(i.2)).
Proof. by rewrite unlock. Qed.
Lemma v2tv2E v : v2tv2 v =
  \sum_i [<tv2v x ''(i.1) ⊗v tv2v y ''(i.2) ; v>] *: (''(i.1) ⊗t ''(i.2)).
Proof. by rewrite unlock. Qed.

Lemma tv2v2_is_linear : linear tv2v2.
Proof. 
move=>a f g; rewrite !tv2v2E linear_sum/= -big_split/=; apply eq_bigr=>i _.
by rewrite linearP/= scalerDl scalerA.
Qed.
Canonical tv2v2_additive := Additive tv2v2_is_linear.
Canonical tv2v2_linear := Linear tv2v2_is_linear.
Lemma v2tv2_is_linear : linear v2tv2.
Proof. 
move=>a f g; rewrite !v2tv2E linear_sum/= -big_split/=; apply eq_bigr=>i _.
by rewrite linearP/= scalerDl scalerA.
Qed.
Canonical v2tv2_additive := Additive v2tv2_is_linear.
Canonical v2tv2_linear := Linear v2tv2_is_linear.
Lemma tv2v2Z c v : tv2v2 (c *: v) = c *: tv2v2 v. Proof. exact: linearZ. Qed.
Lemma v2tv2Z c v : v2tv2 (c *: v) = c *: v2tv2 v. Proof. exact: linearZ. Qed.

Lemma eqsymPf (U : eqType) (s t : U) : (t == s) = false -> (s == t) = false.
Proof. by rewrite eq_sym. Qed.

Lemma tv2v2_ten u v : tv2v2 (u ⊗t v) = tv2v x u ⊗v tv2v y v.
Proof.
rewrite tv2v2E pair_bigV/= {2}(onb_vec t2tv_onbasis u) {2}(onb_vec t2tv_onbasis v).
rewrite linear_sum linear_suml/=; apply eq_bigr=>i _.
rewrite linear_sum linear_sumr/=; apply eq_bigr=>j _.
by rewrite !linearZ/= linearZl/= scalerA tentv_dot mulrC.
Qed.
Lemma v2tv2_ten dis u v : v2tv2 (u ⊗v v) = v2tv u ⊗t v2tv v.
Proof.
apply/(intro_onbl t2tv2_onbasis)=>[[i j]].
rewrite v2tv2E/=/tentv_fun/= linear_sum/= (bigD1 (i,j))//= big1
  =>[[m n]/pair_neq/=[/eqsymPf P|/eqsymPf P]|];
rewrite tenv_dot -?disjoint_neqE// dotpZr !tentv_dot !onb_dot ?P ?mul0r ?mulr0//.
by rewrite !eqxx !mulr1 addr0 -{1}(v2tvK u) -{1}(v2tvK v) !tv2v_dot.
Qed.

Lemma tv2v2_pvars2 dis u : tv2v2 u = tv2v (pvars2 dis) u.
Proof.
rewrite (onb_vec t2tv_onbasis u)/= !linear_sum/=; apply eq_bigr=>[[i j]] _.
by rewrite -{2}tentv_t2tv !linearZ/= tv2v2_ten pvars2_t2tv.
Qed.

Lemma tv2v2_dot dis u v : [< tv2v2 u ; tv2v2 v >] = [< u ; v >].
Proof. by rewrite tv2v2_pvars2 tv2v2_pvars2 (tv2v_dot (pvars2 dis)). Qed.

Lemma tv2v2_norm dis u : `|tv2v2 u| = `|u|.
Proof. by rewrite !hnormE tv2v2_dot. Qed.

Definition tv2v2_fun (F : finType) (f : F -> 'Hs (T1 * T2)) i := tv2v2 (f i).
Lemma tv2v2_funE (F : finType) (f : F -> 'Hs (T1 * T2)) i : tv2v2_fun f i = tv2v2 (f i).
Proof. by []. Qed.
Lemma tv2v2_ponb_dot dis (F : finType) (f : 'PONB(F;'Hs (T1 * T2))) i j :
  [< tv2v2_fun f i; tv2v2_fun f j >] = (i == j)%:R.
Proof. by rewrite !tv2v2_funE tv2v2_dot// ponb_dot. Qed.
Lemma tv2v2_onb_dot dis (F : finType) (f : 'ONB(F;'Hs (T1 * T2))) i j :
  [< tv2v2_fun f i; tv2v2_fun f j >] = (i == j)%:R.
Proof. exact: tv2v2_ponb_dot. Qed.
Lemma tv2v2_onb_dim dis (F : finType) (f : 'ONB(F;'Hs (T1 * T2))) :
  #|F| = Vector.dim ('H[H]_(lb x :|: lb y)).
Proof.
by rewrite (onb_card f) dim_setten big_setU//= -ihb_dim_cast card_prod
  -!dim_setten -!vset_dim.
Qed.
Canonical tv2v2_ponbasis dis F f := PONBasis (@tv2v2_ponb_dot dis F f).
Canonical tv2v2_onbasis dis F f := ONBasis (@tv2v2_onb_dot dis F f) (tv2v2_onb_dim dis f).

Lemma v2tv2_dot dis u v : [< v2tv2 u ; v2tv2 v >] = [< u ; v >].
Proof.
rewrite [u](onb_vec (tv2v2_onbasis dis t2tv2_onbasis)) linear_sum/= !dotp_suml.
apply eq_bigr=>[[i j] _]/=; rewrite [v](onb_vec (tv2v2_onbasis dis t2tv2_onbasis)) 
linear_sum/= !dotp_sumr; apply eq_bigr=>[[m n] _]/=.
rewrite /=/tv2v2_fun/tentv_fun/= !linearZ/= !dotpZl.
by rewrite !tv2v2_ten !v2tv2_ten// tentv_dot !v2tv_dot tenv_dot -?disjoint_neqE.
Qed.

Definition v2tv2_fun (F : finType) (f : F -> 'H_(lb x :|: lb y)) i := v2tv2 (f i).
Lemma v2tv2_funE (F : finType) (f : F -> 'H_(lb x :|: lb y)) i : v2tv2_fun f i = v2tv2 (f i).
Proof. by []. Qed.
Lemma v2tv2_ponb_dot dis (F : finType) (f : 'PONB(F;'H_(lb x :|: lb y))) i j :
  [< v2tv2_fun f i; v2tv2_fun f j >] = (i == j)%:R.
Proof. by rewrite !v2tv2_funE v2tv2_dot// ponb_dot. Qed.
Lemma v2tv2_onb_dot dis (F : finType) (f : 'ONB(F;'H_(lb x :|: lb y))) i j :
  [< v2tv2_fun f i; v2tv2_fun f j >] = (i == j)%:R.
Proof. exact: v2tv2_ponb_dot. Qed.
Lemma v2tv2_onb_dim dis (F : finType) (f : 'ONB(F;'H[H]_(lb x :|: lb y))) :
  #|F| = Vector.dim ('Hs (T1 * T2)).
Proof.
by rewrite (onb_card f) -(tv2v2_onb_dim dis t2tv2_onbasis) (onb_card t2tv2_onbasis).
Qed.
Canonical v2tv2_ponbasis dis F f := PONBasis (@v2tv2_ponb_dot dis F f).
Canonical v2tv2_onbasis dis F f := ONBasis (@v2tv2_onb_dot dis F f) (v2tv2_onb_dim dis f).

Lemma tv2v2K dis : cancel tv2v2 v2tv2.
Proof.
move=>a. apply/(intro_onbl t2tv2_onbasis)=>[[i j]].
rewrite/=/tentv_fun/= -{1}(tv2vK x ''i) -{1}(tv2vK y ''j) -v2tv2_ten=>[//|].
by rewrite v2tv2_dot// -tv2v2_ten tv2v2_dot.
Qed.
Lemma v2tv2K dis : cancel v2tv2 tv2v2.
Proof.
move=>a; apply/(intro_onbl (tv2v2_onbasis dis t2tv2_onbasis))=>[[i j]].
rewrite/=/tv2v2_fun/tentv_fun/= tv2v2_dot// -{1}(tv2vK x ''i) -{1}(tv2vK y ''j).
by rewrite -v2tv2_ten// v2tv2_dot// tv2v2_ten.
Qed.
Lemma tv2v2_inj dis : injective tv2v2. Proof. exact: (can_inj (tv2v2K dis)). Qed.
Lemma v2tv2_inj dis : injective v2tv2. Proof. exact: (can_inj (v2tv2K dis)). Qed.

Lemma tv2v2_conj u : (tv2v2 u)^*v = tv2v2 u^*v.
Proof.
rewrite !tv2v2E linear_sum/=; apply eq_bigr=>i _.
by rewrite conjvZ -tenv_conj conj_dotp -conjv_dot tentv_conj ?tv2v_conj !t2tv_conj.
Qed.

Fact tf2f2_key : unit. Proof. by []. Qed.
Definition tf2f2 (f : 'End('Hs (T1 * T2))) : 'F[H]_(lb x :|: lb y) :=
  locked_with tf2f2_key (\sum_i\sum_j [<''(i.1) ⊗t ''(i.2) ; f (''(j.1) ⊗t ''(j.2)) >] *: 
    [>tv2v x ''(i.1) ⊗v tv2v y ''(i.2) ; tv2v x ''(j.1) ⊗v tv2v y ''(j.2) <]).
Canonical tf2f2_unlockable f := [unlockable of tf2f2 f].
Fact f2tf2_key : unit. Proof. by []. Qed.
Definition f2tf2 (f : 'F[H]_(lb x :|: lb y)) : 'End('Hs (T1 * T2)) :=
  locked_with f2tf2_key (\sum_i\sum_j [<tv2v x ''(i.1) ⊗v tv2v y ''(i.2) ; 
    f (tv2v x ''(j.1) ⊗v tv2v y ''(j.2)) >] *: [>''(i.1) ⊗t ''(i.2) ; ''(j.1) ⊗t ''(j.2) <]).
Canonical f2tf2_unlockable f := [unlockable of f2tf2 f].

Lemma tf2f2E f : tf2f2 f = \sum_i\sum_j [<''(i.1) ⊗t ''(i.2) ; f (''(j.1) ⊗t ''(j.2)) >] *: 
  [>tv2v x ''(i.1) ⊗v tv2v y ''(i.2) ; tv2v x ''(j.1) ⊗v tv2v y ''(j.2) <].
Proof. by rewrite unlock. Qed.
Lemma f2tf2E f : f2tf2 f = \sum_i\sum_j [<tv2v x ''(i.1) ⊗v tv2v y ''(i.2) ; 
  f (tv2v x ''(j.1) ⊗v tv2v y ''(j.2)) >] *: [>''(i.1) ⊗t ''(i.2) ; ''(j.1) ⊗t ''(j.2) <].
Proof. by rewrite unlock. Qed.

Lemma f2tf2_is_linear : linear f2tf2.
Proof. 
move=>a b c; rewrite !f2tf2E; do 2 (rewrite linear_sum/= -big_split/=; apply eq_bigr=>? _).
by rewrite lfunE/= lfunE/= dotpDr dotpZr scalerA scalerDl.
Qed.
Canonical f2tf2_linear := Linear f2tf2_is_linear.
Lemma tf2f2_is_linear : linear tf2f2.
Proof. 
move=>a b c; rewrite !tf2f2E; do 2 (rewrite linear_sum/= -big_split/=; apply eq_bigr=>? _).
by rewrite lfunE/= lfunE/= dotpDr dotpZr scalerA scalerDl.
Qed.
Canonical tf2f2_linear := Linear tf2f2_is_linear.

Lemma tf2f2_ten u v : tf2f2 (u ⊗f v) = tf2f x u \⊗ tf2f y v.
Proof.
rewrite {2}(onb_lfun2id t2tv_onbasis u) exchange_big tf2f2E linear_sum/= linear_suml/= pair_bigV/=.
apply eq_bigr=>i _; rewrite exchange_big/= linear_sum/= linear_suml/= pair_bigV/=.
apply eq_bigr=>j _; rewrite {2}(onb_lfun2id t2tv_onbasis v) !linear_sum/=.
apply eq_bigr=>m _; rewrite !linear_sum/=; apply eq_bigr=>n _.
by rewrite tentf_apply tentv_dot 2 !linearZ/= tenfZl tenfZr scalerA -tenf_outp !tv2v_out.
Qed.

Lemma f2tf2_ten dis u v : f2tf2 (u \⊗ v) = f2tf u ⊗f f2tf v.
Proof.
apply/(intro_onb t2tv2_onbasis)=>[[i j]]; apply/(intro_onbl t2tv2_onbasis)=>[[m n]].
rewrite/=/tentv_fun/= tentf_apply tentv_dot f2tf2E sum_lfunE linear_sum/=.
rewrite (bigD1 (m,n))//= sum_lfunE (bigD1 (i,j))//= !big1=>
  [[a b]/pair_neq/=[P|P]|[a b]/pair_neq/=[/eqsymPf P|/eqsymPf P]|].
3,4: rewrite sum_lfunE dotp_sumr big1 ?linear0//==>[[c d] _].
all: rewrite ?addr0 lfunE/= outpE ?dotpZr ?tentv_dot ?onb_dot ?P ?(mulr0,mul0r)// ?scale0r ?scaler0//.
rewrite !eqxx !mulr1 tenf_apply ?tenv_dot -?disjoint_neqE//.
by rewrite -{1}(f2tfK u) -{1}(f2tfK v) !tf2f_apply !tv2v_dot.
Qed.

Lemma tf2f2_apply dis f v : (tf2f2 f) (tv2v2 v) = tv2v2 (f v).
Proof.
rewrite tf2f2E {2}(onb_lfun2id t2tv2_onbasis f) exchange_big/= !sum_lfunE !linear_sum.
apply eq_bigr=>[[i j] _]. rewrite !sum_lfunE linear_sum. apply eq_bigr=>[[m n] _].
rewrite/=/tentv_fun/= !lfunE/= linearZ/=; f_equal.
by rewrite !outpE linearZ/= -!tv2v2_ten tv2v2_dot.
Qed.

Lemma f2tf2_apply dis f v : (f2tf2 f) (v2tv2 v) = v2tv2 (f v).
Proof.
rewrite f2tf2E {2}(onb_lfun2id (tv2v2_onbasis dis t2tv2_onbasis) f) exchange_big/= !sum_lfunE !linear_sum.
apply eq_bigr=>[[i j] _]. rewrite !sum_lfunE linear_sum. apply eq_bigr=>[[m n] _].
rewrite/=/tv2v2_fun/tentv_fun/= !lfunE/= linearZ/= !tv2v2_ten. f_equal.
rewrite !outpE linearZ/= -!tv2v2_ten tv2v2K// -tv2v2_dot// v2tv2K//.
Qed.

Lemma tf2f2_pvars2 dis f : tf2f2 f = tf2f (pvars2 dis) f.
Proof.
apply/(intro_onb (tv2v2_onbasis dis t2tv2_onbasis))=>[[i j]].
by rewrite/=/tv2v2_fun/tentv_fun/= tf2f2_apply// !tv2v2_pvars2 (tf2f_apply (pvars2 dis)).
Qed.

Lemma tf2f2K dis : cancel tf2f2 f2tf2.
Proof.
by move=>f; apply/lfunP=>v; rewrite -{1}(tv2v2K dis v) f2tf2_apply// tf2f2_apply// tv2v2K.
Qed.
Lemma f2tf2K dis : cancel f2tf2 tf2f2.
Proof.
by move=>f; apply/lfunP=>v; rewrite -{1}(v2tv2K dis v) tf2f2_apply// f2tf2_apply// v2tv2K.
Qed.
Lemma tf2f2_inj dis : injective tf2f2. Proof. exact: (can_inj (tf2f2K dis)). Qed.
Lemma f2tf2_inj dis : injective f2tf2. Proof. exact: (can_inj (f2tf2K dis)). Qed.

Lemma tf2f2_adj f : (tf2f2 f)^A = tf2f2 f^A.
Proof.
rewrite !tf2f2E exchange_big linear_sum/=. apply eq_bigr=>i _.
rewrite linear_sum/=; apply eq_bigr=>j _.
by rewrite adjfZ adj_outp conj_dotp adj_dotEV.
Qed.
Lemma tf2f2_conj f : (tf2f2 f)^C = tf2f2 f^C.
Proof.
rewrite !tf2f2E linear_sum/=. apply eq_bigr=>i _.
rewrite linear_sum/=; apply eq_bigr=>j _.
by rewrite conjfZ conj_outp conj_dotp conjfE conjv_dotr !tentv_conj -!tenv_conj !tv2v_conj !t2tv_conj.
Qed.
Lemma tf2f2_tr f : ((tf2f2 f)^T = tf2f2 f^T)%VF.
Proof. by rewrite trfAC tf2f2_adj tf2f2_conj -trfAC. Qed.

Lemma f2tf2_adj f : (f2tf2 f)^A = f2tf2 f^A.
Proof.
rewrite !f2tf2E exchange_big linear_sum/=. apply eq_bigr=>i _.
rewrite linear_sum/=; apply eq_bigr=>j _.
by rewrite adjfZ adj_outp conj_dotp adj_dotEV.
Qed.
Lemma f2tf2_conj f : (f2tf2 f)^C = f2tf2 f^C.
Proof.
rewrite !f2tf2E linear_sum/=. apply eq_bigr=>i _.
rewrite linear_sum/=; apply eq_bigr=>j _.
by rewrite conjfZ conj_outp conj_dotp conjfE conjv_dotr !tentv_conj -!tenv_conj !tv2v_conj !t2tv_conj.
Qed.
Lemma f2tf2_tr f : ((f2tf2 f)^T = f2tf2 f^T)%VF.
Proof. by rewrite trfAC f2tf2_adj f2tf2_conj -trfAC. Qed.

Lemma tf2f2_comp dis f g : tf2f2 f \o tf2f2 g = tf2f2 (f \o g).
Proof. by apply/lfunP=>v; rewrite -(v2tv2K dis v) lfunE/= !tf2f2_apply// lfunE. Qed.
Lemma f2tf2_comp dis f g : f2tf2 f \o f2tf2 g = f2tf2 (f \o g).
Proof. by apply/lfunP=>v; rewrite -(tv2v2K dis v) lfunE/= !f2tf2_apply// lfunE. Qed.

Lemma tf2f21 : tf2f2 \1 = \1.
Proof. by rewrite -tentf11 tf2f2_ten -!tf2f1 tenf11. Qed.
Lemma tf2f20 : tf2f2 0 = 0. Proof. exact: linear0. Qed.
Lemma f2tf21 dis : f2tf2 \1 = \1.
Proof. by rewrite -[RHS](tf2f2K dis) tf2f21. Qed.
Lemma f2tf20 : f2tf2 0 = 0. Proof. exact: linear0. Qed.

Definition tf2f2c (f : 'End('Hs (T1 * T2))) :=
  if [disjoint lb x & lb y] then tf2f2 f else \1.
Lemma tf2f2c_unitary (f : 'FU('Hs (T1 * T2))) :
  tf2f2c f \is unitarylf.
Proof.
rewrite /tf2f2c; case E: ([disjoint lb x & lb y]); last by apply/unitaryf_unitary.
by apply/unitarylfP; rewrite tf2f2_adj tf2f2_comp// unitaryf_form tf2f21.
Qed.
Canonical tf2f2c_unitaryfType f := UnitaryfType (@tf2f2c_unitary f).

Lemma tf2f2c_adj f : (tf2f2c f)^A = tf2f2c f^A.
Proof. by rewrite /tf2f2c [LHS]fun_if adjf1 tf2f2_adj. Qed.
Lemma tf2f2c_tr f : ((tf2f2c f)^T = tf2f2c f^T)%VF.
Proof. by rewrite /tf2f2c [LHS]fun_if trf1 tf2f2_tr. Qed.
Lemma tf2f2c_conj f : (tf2f2c f)^C = tf2f2c f^C.
Proof. by rewrite /tf2f2c [LHS]fun_if conjf1 tf2f2_conj. Qed.

Lemma tf2f2cE dis f : tf2f2c f = tf2f2 f.
Proof. by rewrite /tf2f2c dis. Qed.

Lemma tv2v2_out u v : 
  [> tv2v2 u ; tv2v2 v <] = tf2f2 [> u ; v <].
Proof.
rewrite [u](onb_vec t2tv2_onbasis) [v](onb_vec t2tv2_onbasis)/=/tentv_fun.
rewrite linear_sum !outp_suml !linear_sum; apply eq_bigr=>i _.
rewrite !linear_sum/=; apply eq_bigr=>j _.
rewrite !linearZ/= !linearZl/= !linearZ/=.
by rewrite -tentv_out tf2f2_ten !tv2v2_ten -tenf_outp !tv2v_out.
Qed.

Lemma tf2f2_lef dis u v : tf2f2 u ⊑ tf2f2 v = (u ⊑ v).
Proof.
apply/Bool.eq_iff_eq_true; split=>/lef_dot P;
apply/lef_dot=>f. move: (P (tv2v2 f)). 2: rewrite -(v2tv2K dis f).
all: by rewrite !(tf2f2_apply dis) !(tv2v2_dot dis).
Qed.
Lemma tf2f2_ltf dis u v : tf2f2 u ⊏ tf2f2 v = (u ⊏ v).
Proof. by rewrite !lt_def tf2f2_lef// (can_eq (tf2f2K dis)). Qed.
Lemma tf2f2_le1 dis u : tf2f2 u ⊑ \1 = (u ⊑ \1).
Proof. by rewrite -tf2f21 tf2f2_lef. Qed.
Lemma tf2f2_ge0 dis u : (0 : 'End(_)) ⊑ tf2f2 u = ((0 : 'End(_)) ⊑ u).
Proof. by rewrite -tf2f20 tf2f2_lef. Qed.
Lemma f2tf2_lef dis u v : f2tf2 u ⊑ f2tf2 v = (u ⊑ v).
Proof. by rewrite -(tf2f2_lef dis) !f2tf2K. Qed.
Lemma f2tf2_ltf dis u v : f2tf2 u ⊏ f2tf2 v = (u ⊏ v).
Proof. by rewrite -(tf2f2_ltf dis) !f2tf2K. Qed.

(* if vars are the same, doing nothing *)
Fact tm2m2_key : unit. Proof. by []. Qed.
Definition tm2m2 (F : finType) (f : F -> 'End[T1*T2]) := 
  locked_with tm2m2_key
  (fun i : F => if [disjoint lb x & lb y] then tf2f2 (f i) else (sqrtC (#|F|%:R))^-1 *: \1).
Canonical tm2m2_unlockable F f := [unlockable fun @tm2m2 F f].
Lemma tm2m2_tn (F : finType) (f : 'TN(F;'Hs (T1 * T2))) : trace_nincr (tm2m2 f).
Proof.
rewrite unlock /trace_nincr; case E: [disjoint lb x & lb y].
  under eq_bigr do rewrite tf2f2_adj (tf2f2_comp E).
  by rewrite -linear_sum/= tf2f2_le1//; apply/tn_tnP.
rewrite sumr_const cardT -cardT adjfZ -comp_lfunZl -comp_lfunZr adjf1 comp_lfun1l.
rewrite -scaler_nat !scalerA !divc_simp. case: (#|F|)=>[|n].
by rewrite mul0r scale0r lef01. by rewrite mulfV// scale1r.
Qed.
Canonical tm2m2_tnType F f := TNType (@tm2m2_tn F f).
Lemma tm2m2_tp (F : finType) (f : 'QM(F;'Hs (T1 * T2))) : trace_presv (tm2m2 f).
Proof.
rewrite unlock /trace_presv; case E: [disjoint lb x & lb y].
  under eq_bigr do rewrite tf2f2_adj (tf2f2_comp E).
  by rewrite -linear_sum/= qm_tpE tf2f21.
rewrite sumr_const cardT -cardT adjfZ -comp_lfunZl -comp_lfunZr adjf1 comp_lfun1l.
rewrite -scaler_nat !scalerA !divc_simp mulfV ?scale1r//.
case: eqP=>//=/eqP; rewrite pnatr_eq0=>/eqP/card0_eq P.
by move: (qm_tpE f)=>/eqP; rewrite big_pred0// eq_sym oner_eq0.
Qed.
Canonical tm2m2_qmType F f := QMType (@tm2m2_tp F f).
Lemma tm2m2E dis (F : finType) (f : F -> 'End[T1*T2]) i : 
  tm2m2 f i = tf2f2 (f i).
Proof. by rewrite unlock dis. Qed.

End Inject.

Section SyntaxWithType.
Implicit Type (S : {set L}).
Notation cmd_ := (@cmd_ L H).
Notation seqc := (@seqc_ L H).
Notation skip := (@skip_ L H).

Definition initt_ T (x : vars T) (v : 'NS('Hs T)) :=
  init_ [NS of tv2v x v].

Definition unitaryt_ T (x : vars T) (U : 'FU('Hs T)) :=
  unitary_ [unitary of tf2f x U].

Definition unitaryt2_ T1 T2 (x : vars T1) (y : vars T2) (U : 'FU('Hs (T1 * T2))) :=
  unitary_ [unitary of tf2f2c x y U].

Definition condt_ (F : finType) T (x : vars T) (M : 'QM(F;'Hs T)) (c : F -> cmd_) :=
  cond_ [QM of tm2m x M] c.

Definition condt2_ (F : finType) T1 T2 (x : vars T1) (y : vars T2) 
  (M : 'QM(F;'Hs (T1 * T2))) (c : F -> cmd_) :=
  cond_ [QM of tm2m2 x y M] c.

Definition whilet_ T (x : vars T) (M : 'QM(bool;'Hs T)) b (c : cmd_) :=
  while_ [QM of tm2m x M] b c.

Definition whilet2_ T1 T2 (x : vars T1) (y : vars T2) 
  (M : 'QM(bool;'Hs (T1 * T2))) b (c :  cmd_) :=
  while_ [QM of tm2m2 x y M] b c.

End SyntaxWithType.
End Inject.

Notation "[ 'it' x ':=' v ]" := (initt_ x [NS of v]) 
  (at level 0, no associativity, format "[ 'it'  x  ':='  v ]") : lfun_scope.
Notation "[ 'ut' x ':=' U ]" := (unitaryt_ x [unitary of U])
  (at level 0, no associativity, format "[ 'ut'  x  ':='  U ]") : lfun_scope.
Notation "[ 'ut' [ x , y ] ':=' U ]" := (unitaryt2_ x y [unitary of U])
  (at level 0, no associativity, format "[ 'ut'  [ x ,  y ]  ':='  U ]") : lfun_scope.
Notation "[ 'if' M [ x ] '=' t 'then' F ]" := (condt_ x [QM of M] (fun t=>F)) 
  (at level 0, right associativity, format
    "[ 'if' M [ x ] '=' t 'then' F ]") : lfun_scope.
Notation "[ 'if' M [ x , y ] '=' t 'then' F ]" := (condt2_ x y [QM of M] (fun t=>F)) 
  (at level 0, right associativity, format
    "[ 'if' M [ x , y ] '=' t 'then' F ]") : lfun_scope.
Notation "[ 'while' M [ x ] '=' b 'do' c ]" := (whilet_ x [QM of M] b c) 
  (at level 0, right associativity, format
    "[ 'while'  M [ x ]  '='  b  'do'  c ]") : lfun_scope.
Notation "[ 'while' M [ x , y ] '=' b 'do' c ]" := (whilet2_ x y [QM of M] b c) 
  (at level 0, right associativity, format
    "[ 'while'  M [ x , y ]  '='  b  'do'  c ]") : lfun_scope.

Section HoareTriple.
Context (L : finType) (H : L -> chsType).
Local Notation cmd := (cmd_ H).
Local Open Scope qexpr_scope.

(* predicates are observables over full space : 'FO[H]_setT *)
(* there are two boolean variables, pt : false - partial , true - toal *)
(* st : false - may not saturated , true saturated (the weakest (literal) precondition)*)
(* pt and st are introduced to avoid messy amount of rules *)
Definition global_hoare (pt st : bool) (P: 'FO[H]_setT) (Q: 'FO[H]_setT) (c: cmd) :=
  (forall (x : 'FD[H]_setT),
  if pt then
    if st then \Tr (P \o x) = \Tr (Q \o ((fsem c) x))
          else \Tr (P \o x) <= \Tr (Q \o ((fsem c) x))
  else
    if st then \Tr (Q^⟂ \o ((fsem c) x)) = \Tr (P^⟂ \o x)
          else \Tr (Q^⟂ \o ((fsem c) x)) <= \Tr (P^⟂ \o x)  ).

Definition local_hoare (pt st : bool) S T (P: 'F[H]_S) (Q: 'F[H]_T) (c: cmd) :=
  (forall (x : 'FD[H]_setT),
  if pt then
    if st then \Tr (liftf_lf P \o x) = \Tr (liftf_lf Q \o ((fsem c) x))
          else \Tr (liftf_lf P \o x) <= \Tr (liftf_lf Q \o ((fsem c) x))
  else
    if st then \Tr (liftf_lf Q^⟂ \o ((fsem c) x)) = \Tr (liftf_lf P^⟂ \o x)
          else \Tr (liftf_lf Q^⟂ \o ((fsem c) x)) <= \Tr (liftf_lf P^⟂ \o x)  ).

Definition qexpr_hoare (pt st : bool) (P Q : 'QE[H]) (c: cmd) :=
  exists S T, (qesqr S P /\ qesqr T Q /\ local_hoare pt st (P S S) (Q T T) c).

Definition state_hoare (pt st : bool) (P Q : 'QE[H]) (c: cmd) :=
  qexpr_hoare pt st (P ∗ P`A) (Q ∗ Q`A) c.

End HoareTriple.

Notation "'⊨pg' { P } c { Q }" := (global_hoare false false P Q c)
  (at level 10, P,c,Q at next level, format "'⊨pg' {  P  }  c  {  Q  }" ).
Notation "'⊫pg' { P } c { Q }" := (global_hoare false true P Q c)
  (at level 10, P,c,Q at next level, format "'⊫pg' {  P  }  c  {  Q  }" ).
Notation "'⊨tg' { P } c { Q }" := (global_hoare true false P Q c)
  (at level 10, P,c,Q at next level, format "'⊨tg' {  P  }  c  {  Q  }" ).
Notation "'⊫tg' { P } c { Q }" := (global_hoare true true P Q c)
  (at level 10, P,c,Q at next level, format "'⊫tg' {  P  }  c  {  Q  }" ).
Notation "'⊨g' [ pt ] { P } c { Q }" := (global_hoare pt false P Q c)
  (at level 10, pt,P,c,Q at next level, format "'⊨g' [ pt ] {  P  }  c  {  Q  }" ).
Notation "'⊫g' [ pt ] { P } c { Q }" := (global_hoare pt true P Q c)
  (at level 10, pt,P,c,Q at next level, format "'⊫g' [ pt ] {  P  }  c  {  Q  }" ).
Notation "'⊨pg' [ st ] { P } c { Q }" := (global_hoare false st P Q c)
  (at level 10, st,P,c,Q at next level, format "'⊨pg' [ st ] {  P  }  c  {  Q  }" ).
Notation "'⊨tg' [ st ] { P } c { Q }" := (global_hoare true st P Q c)
  (at level 10, st,P,c,Q at next level, format "'⊨tg' [ st ] {  P  }  c  {  Q  }" ).
Notation "'⊨g' [ pt , st ] { P } c { Q }" := (global_hoare pt st P Q c)
  (at level 10, pt,st,P,c,Q at next level, format "'⊨g' [ pt , st ] {  P  }  c  {  Q  }" ).

Notation "'⊨pl' { P } c { Q }" := (local_hoare false false P Q c)
  (at level 10, P,c,Q at next level, format "'⊨pl' {  P  }  c  {  Q  }" ).
Notation "'⊫pl' { P } c { Q }" := (local_hoare false true P Q c)
  (at level 10, P,c,Q at next level, format "'⊫pl' {  P  }  c  {  Q  }" ).
Notation "'⊨tl' { P } c { Q }" := (local_hoare true false P Q c)
  (at level 10, P,c,Q at next level, format "'⊨tl' {  P  }  c  {  Q  }" ).
Notation "'⊫tl' { P } c { Q }" := (local_hoare true true P Q c)
  (at level 10, P,c,Q at next level, format "'⊫tl' {  P  }  c  {  Q  }" ).
Notation "'⊨l' [ pt ] { P } c { Q }" := (local_hoare pt false P Q c)
  (at level 10, pt,P,c,Q at next level, format "'⊨l' [ pt ] {  P  }  c  {  Q  }" ).
Notation "'⊫l' [ pt ] { P } c { Q }" := (local_hoare pt true P Q c)
  (at level 10, pt,P,c,Q at next level, format "'⊫l' [ pt ] {  P  }  c  {  Q  }" ).
Notation "'⊨pl' [ st ] { P } c { Q }" := (local_hoare false st P Q c)
  (at level 10, st,P,c,Q at next level, format "'⊨pl' [ st ] {  P  }  c  {  Q  }" ).
Notation "'⊨tl' [ st ] { P } c { Q }" := (local_hoare true st P Q c)
  (at level 10, st,P,c,Q at next level, format "'⊨tl' [ st ] {  P  }  c  {  Q  }" ).
Notation "'⊨l' [ pt , st ] { P } c { Q }" := (local_hoare pt st P Q c)
  (at level 10, pt,st,P,c,Q at next level, format "'⊨l' [ pt , st ] {  P  }  c  {  Q  }" ).

Notation "'⊨p' { P } c { Q }" := (qexpr_hoare false false P Q c)
  (at level 10, P,c,Q at next level, format "'⊨p' {  P  }  c  {  Q  }" ).
Notation "'⊫p' { P } c { Q }" := (qexpr_hoare false true P Q c)
  (at level 10, P,c,Q at next level, format "'⊫p' {  P  }  c  {  Q  }" ).
Notation "'⊨t' { P } c { Q }" := (qexpr_hoare true false P Q c)
  (at level 10, P,c,Q at next level, format "'⊨t' {  P  }  c  {  Q  }" ).
Notation "'⊫t' { P } c { Q }" := (qexpr_hoare true true P Q c)
  (at level 10, P,c,Q at next level, format "'⊫t' {  P  }  c  {  Q  }" ).
Notation "'⊨' [ pt ] { P } c { Q }" := (qexpr_hoare pt false P Q c)
  (at level 10, pt,P,c,Q at next level, format "'⊨' [ pt ] {  P  }  c  {  Q  }" ).
Notation "'⊫' [ pt ] { P } c { Q }" := (qexpr_hoare pt true P Q c)
  (at level 10, pt,P,c,Q at next level, format "'⊫' [ pt ] {  P  }  c  {  Q  }" ).
Notation "'⊨p' [ st ] { P } c { Q }" := (qexpr_hoare false st P Q c)
  (at level 10, st,P,c,Q at next level, format "'⊨p' [ st ] {  P  }  c  {  Q  }" ).
Notation "'⊨t' [ st ] { P } c { Q }" := (qexpr_hoare true st P Q c)
  (at level 10, st,P,c,Q at next level, format "'⊨t' [ st ] {  P  }  c  {  Q  }" ).
Notation "'⊨' [ pt , st ] { P } c { Q }" := (qexpr_hoare pt st P Q c)
  (at level 10, pt,st,P,c,Q at next level, format "'⊨' [ pt , st ] {  P  }  c  {  Q  }" ).

Notation "'⊨ps' { P } c { Q }" := (state_hoare false false P Q c)
  (at level 10, P,c,Q at next level, format "'⊨ps' {  P  }  c  {  Q  }" ).
Notation "'⊫ps' { P } c { Q }" := (state_hoare false true P Q c)
  (at level 10, P,c,Q at next level, format "'⊫ps' {  P  }  c  {  Q  }" ).
Notation "'⊨ts' { P } c { Q }" := (state_hoare true false P Q c)
  (at level 10, P,c,Q at next level, format "'⊨ts' {  P  }  c  {  Q  }" ).
Notation "'⊫ts' { P } c { Q }" := (state_hoare true true P Q c)
  (at level 10, P,c,Q at next level, format "'⊫ts' {  P  }  c  {  Q  }" ).
Notation "'⊨s' [ pt ] { P } c { Q }" := (state_hoare pt false P Q c)
  (at level 10, pt,P,c,Q at next level, format "'⊨s' [ pt ] {  P  }  c  {  Q  }" ).
Notation "'⊫s' [ pt ] { P } c { Q }" := (state_hoare pt true P Q c)
  (at level 10, pt,P,c,Q at next level, format "'⊫s' [ pt ] {  P  }  c  {  Q  }" ).
Notation "'⊨ps' [ st ] { P } c { Q }" := (state_hoare false st P Q c)
  (at level 10, st,P,c,Q at next level, format "'⊨ps' [ st ] {  P  }  c  {  Q  }" ).
Notation "'⊨ts' [ st ] { P } c { Q }" := (state_hoare true st P Q c)
  (at level 10, st,P,c,Q at next level, format "'⊨ts' [ st ] {  P  }  c  {  Q  }" ).
Notation "'⊨s' [ pt , st ] { P } c { Q }" := (state_hoare pt st P Q c)
  (at level 10, pt,st,P,c,Q at next level, format "'⊨s' [ pt , st ] {  P  }  c  {  Q  }" ).

Add Parametric Morphism L H pt st P Q : 
  (@global_hoare L H pt st P Q)
  with signature (@eqcmd L H) ==> iff as eqcmd_hoare_mor.
Proof.
move=>x y; rewrite /eqcmd=>H1; split=>P1 z.
rewrite -H1; apply P1. rewrite H1; apply P1.
Qed.

Add Parametric Morphism L H pt st S T P Q : 
  (@local_hoare L H pt st S T P Q)
  with signature (@eqcmd L H) ==> iff as eqcmd_local_hoare_mor.
Proof.
move=>x y; rewrite /eqcmd=>H1; split=>P1 z.
rewrite -H1; apply P1. rewrite H1; apply P1.
Qed.

Add Parametric Morphism L H pt st (P Q : 'QE[H]) : 
  (@qexpr_hoare L H pt st P Q)
  with signature (@eqcmd L H) ==> iff as eqcmd_qexpr_hoare_mor.
Proof.
by move=>x y Pxy; split; move=>[S[T[Ps[Pt Px]]]]; 
exists S; exists T; do 2 split=>//; move: Px; rewrite Pxy.
Qed.

Add Parametric Morphism L H pt st (P Q : 'QE[H]) : 
  (@state_hoare L H pt st P Q)
  with signature (@eqcmd L H) ==> iff as eqcmd_qexpr_hoare_form_mor.
Proof. by move=>x y Pxy; rewrite/state_hoare Pxy. Qed.

Section TrivalHoare.
Context (L : finType) (H : L -> chsType).
Implicit Type (c : @cmd_ L H).
Local Open Scope qexpr_scope.

Lemma saturated_strong_G pt st P Q c :
  ⊫g [ pt ] { P } c { Q } -> ⊨g [ pt , st ] { P } c { Q }.
Proof. by case: st=>//; case: pt=>P1 x; rewrite P1. Qed.
Lemma saturated_strong_L pt st S T (P: 'F[H]_S) (Q: 'F[H]_T) c :
  ⊫l [ pt ] { P } c { Q } -> ⊨l [ pt , st ] { P } c { Q }.
Proof. by case: st=>//; case: pt=>P1 x; rewrite P1. Qed.
Lemma saturated_strong pt st (P: 'QE[H]) (Q: 'QE[H]) c :
  ⊫ [ pt ] { P } c { Q } -> ⊨ [ pt , st ] { P } c { Q }.
Proof.
move=>[S[T[Ps[Pt Pl]]]]; exists S; exists T; 
by do 2 split=>//; apply/saturated_strong_L.
Qed.
Lemma saturated_strongS pt st (P: 'QE[H]) (Q: 'QE[H]) c :
  ⊫s [ pt ] { P } c { Q } -> ⊨s [ pt , st ] { P } c { Q }.
Proof. exact: saturated_strong. Qed.

Lemma saturated_weak_G pt st P Q c :
  ⊨g [ pt , st ] { P } c { Q } -> ⊨g [ pt ] { P } c { Q }.
Proof. case: st=>//; exact: saturated_strong_G. Qed.
Lemma saturated_weak_L pt st S T (P: 'F[H]_S) (Q: 'F[H]_T) c :
  ⊨l [ pt , st ] { P } c { Q } -> ⊨l [ pt ] { P } c { Q }.
Proof. case: st=>//; exact: saturated_strong_L. Qed.
Lemma saturated_weak pt st (P: 'QE[H]) (Q: 'QE[H]) c :
  ⊨ [ pt , st ] { P } c { Q } -> ⊨ [ pt ] { P } c { Q }.
Proof. case: st=>//; exact: saturated_strong. Qed.
Lemma saturated_weakS pt st (P: 'QE[H]) (Q: 'QE[H]) c :
  ⊨s [ pt , st ] { P } c { Q } -> ⊨s [ pt ] { P } c { Q }.
Proof. case: st=>//; exact: saturated_strongS. Qed.

Lemma partial_alter_G (st : bool) (P: 'FO[H]_setT) (Q: 'FO[H]_setT) c :
  ⊨g [ false , st ] { P } c { Q } <-> 
  (forall (x : 'FD[H]_setT), 
  if st then \Tr (P \o x) = \Tr (Q \o ((fsem c) x)) + \Tr x - \Tr ((fsem c) x)
        else \Tr (P \o x) <= \Tr (Q \o ((fsem c) x)) + \Tr x - \Tr ((fsem c) x) ).
Proof.
case: st; split=>H1 x; move: (H1 x); rewrite -[in \Tr (fsem c x)](comp_lfun1l (fsem c x))
  addrAC -linearB/= -linearBl/= -opprB cplmtE linearNl/= linearN/=.
move=>->. 2: move=>/eqP; rewrite -subr_eq -eqr_oppLR=>/eqP<-.
1,2: by rewrite linearBl/= comp_lfun1l !linearB/= opprK addrC// addrA addrN add0r.
all: by rewrite -[\Tr x]opprK ler_subr_addr ler_oppr opprB 
  -[in \Tr x](comp_lfun1l x) -linearB/= -linearBl/= cplmtE.
Qed.

Lemma partial_alter_L (st : bool) S T (P: 'F[H]_S) (Q: 'F[H]_T) c :
  ⊨l [ false , st ] { P } c { Q } <-> 
  (forall (x : 'FD[H]_setT), 
  if st then \Tr (liftf_lf P \o x) = \Tr (liftf_lf Q \o ((fsem c) x)) + \Tr x - \Tr ((fsem c) x)
        else \Tr (liftf_lf P \o x) <= \Tr (liftf_lf Q \o ((fsem c) x)) + \Tr x - \Tr ((fsem c) x) ).
Proof.
case: st; split=>H1 x; move: (H1 x); rewrite -[in \Tr (fsem c x)](comp_lfun1l (fsem c x))
  addrAC -linearB/= -linearBl/= -opprB cplmtE linearNl/= linearN/= !liftf_lf_cplmt.
move=>->. 2: move=>/eqP; rewrite -subr_eq -eqr_oppLR=>/eqP<-.
1,2: by rewrite linearBl/= comp_lfun1l !linearB/= opprK addrC// addrA addrN add0r.
all: by rewrite -[\Tr x]opprK ler_subr_addr ler_oppr opprB 
  -[in \Tr x](comp_lfun1l x) -linearB/= -linearBl/= cplmtE.
Qed.

Lemma relation_GPT st c P Q : 
  fsem c \is isqc -> ⊨g [false,st] { P } c { Q } <-> ⊨g [true,st] { P } c { Q }.
Proof.
move=>IH; rewrite partial_alter_G; split=>H1 x; move: (H1 x);
by rewrite (qc_qcE IH) qc_trlfE addrK.
Qed.
Global Arguments relation_GPT [st c P Q].

Lemma no_while_GPT st c P Q : no_while c ->
  ⊨g [false,st] { P } c { Q } <-> ⊨g [true,st] { P } c { Q }.
Proof. move=>/no_while_qc; exact: relation_GPT. Qed.
Global Arguments no_while_GPT [st c P Q].

Lemma relation_LPT st c S T (P: 'F[H]_S) (Q: 'F[H]_T) : 
  fsem c \is isqc -> ⊨l [false,st] { P } c { Q } <-> ⊨l [true,st] { P } c { Q }.
Proof.
move=>IH; rewrite partial_alter_L; split=>H1 x; move: (H1 x);
by rewrite (qc_qcE IH) qc_trlfE addrK.
Qed.
Global Arguments relation_LPT [st c S T P Q].

Lemma no_while_LPT st c S T (P: 'F[H]_S) (Q: 'F[H]_T) : no_while c ->
  ⊨l [false,st] { P } c { Q } <-> ⊨l [true,st] { P } c { Q }.
Proof. move=>/no_while_qc; exact: relation_LPT. Qed.
Global Arguments no_while_LPT [st c S T P Q].

Lemma relation_PT st c (P Q : 'QE[H]) : 
  fsem c \is isqc -> ⊨ [false,st] { P } c { Q } <-> ⊨ [true,st] { P } c { Q }.
Proof.
split; move=>[S] [T] [PS] [PT] IH; exists S; exists T; do 2 split=>//.
by rewrite -relation_LPT. by rewrite relation_LPT.
Qed.
Global Arguments relation_PT [st c P Q].

Lemma no_while_PT st c (P Q : 'QE[H]) : no_while c ->
  ⊨ [false,st] { P } c { Q } <-> ⊨ [true,st] { P } c { Q }.
Proof. move=>/no_while_qc; exact: relation_PT. Qed.
Global Arguments no_while_PT [st c P Q].

Lemma relation_SPT st c (P Q : 'QE[H]) : 
  fsem c \is isqc -> ⊨s [false,st] { P } c { Q } <-> ⊨s [true,st] { P } c { Q }.
Proof. exact: relation_PT. Qed.
Global Arguments relation_SPT [st c P Q].

Lemma no_while_SPT st c (P Q : 'QE[H]) : no_while c ->
  ⊨s [false,st] { P } c { Q } <-> ⊨s [true,st] { P } c { Q }.
Proof. exact: no_while_PT. Qed.
Global Arguments no_while_SPT [st c P Q].

End TrivalHoare.

Local Open Scope qexpr_scope.

Notation "'｜' v ; x '〉'" := (ketqe (tv2v x v)) 
  (at level 10, format "'｜' v ;  x '〉'", no associativity).
Notation "'〈' v ; x '｜'" := (braqe (tv2v x v)) 
  (at level 10, format "'〈' v ;  x '｜'").
Notation "'｜' v '〉' x '〈' u '｜' " := ((ketqe (tv2v x v)) ∗ (braqe (tv2v x u)))
  (at level 10, x at next level, format "'｜' v '〉' x '〈' u '｜'").
Notation "'⌈' M ; x '⌉'" := (linqe (tf2f x M)) 
  (at level 10, format "'⌈' M ;  x '⌉'").
Notation "'｜' v ; ( x ) '〉'" := (｜ v ; x 〉) 
  (at level 10, only parsing).
Notation "'〈' v ; ( x ) '｜'" := (〈 v ; x ｜) 
  (at level 10, only parsing).
Notation "'｜' v '〉' ( x ) '〈' u '｜'" := (｜ v 〉 x 〈 u ｜) 
  (at level 10, only parsing).
Notation "'⌈' M ; ( x ) '⌉'" := (⌈ M ; x ⌉) 
  (at level 10, only parsing).
Notation "'｜' v ; ( x , y ) '〉'" := (ketqe (tv2v2 x y v)) 
  (at level 10, format "'｜' v ; ( x , y ) '〉'").
Notation "'〈' v ; ( x , y ) '｜'" := (braqe (tv2v2 x y v)) 
  (at level 10, format "'〈' v ; ( x , y ) '｜'").
Notation " '｜' v '〉' ( x , y ) '〈' u '｜' " := (ketqe (tv2v2 x y v) ∗ braqe (tv2v2 x y v))
  (at level 10, x,y at next level, only parsing).
Notation "'⌈' M ; ( x , y ) '⌉'" := (linqe (tf2f2 x y M))
  (at level 10, format "'⌈' M ; ( x , y ) '⌉'").

(* fill the gap : qexpr and tv2v tf2f tv2v2 tf2f2 *)
Section QExprExtra.
Local Open Scope qexpr_scope.
Context (L : finType) (H : L -> chsType).
Notation vars T := (@tvars_of L H _ (Phant T)).
Variable (T T1 T2 : ihbFinType) (x : vars T) (x1 : vars T1) (x2 : vars T2) 
  (dis : [disjoint lb x1 & lb x2]).
Implicit Type (c : C).

Lemma t1lin0 : ⌈ 0; x ⌉ = 0.
Proof. by rewrite !linear0/=. Qed.
Lemma t2lin0 : ⌈ 0; (x1,x2) ⌉ = 0.
Proof. by rewrite !linear0/=. Qed.
Definition tlin0 := (t1lin0, t2lin0).

Lemma t1linN (M : 'End[T]) : - ⌈ M; x ⌉ = ⌈ - M; x ⌉.
Proof. by rewrite !linearN/=. Qed.
Lemma t2linN (M : 'End[T1 * T2]) : - ⌈ M; (x1,x2) ⌉ = ⌈ - M; (x1,x2) ⌉.
Proof. by rewrite !linearN/=. Qed.
Definition tlinN := (t1linN, t2linN).

Lemma t1linD (M1 M2 : 'End[T]) : ⌈ M1; x ⌉ + ⌈ M2; x ⌉ = ⌈ M1 + M2; x ⌉.
Proof. by rewrite !linearD/=. Qed.
Lemma t2linD (M1 M2 : 'End[T1 * T2]) : ⌈ M1; (x1,x2) ⌉ + ⌈ M2; (x1,x2) ⌉ = ⌈ M1 + M2; (x1,x2) ⌉.
Proof. by rewrite !linearD/=. Qed.
Definition tlinD := (t1linD, t2linD).

Lemma t1linB (M1 M2 : 'End[T]) : ⌈ M1; x ⌉ - ⌈ M2; x ⌉ = ⌈ M1 - M2; x ⌉.
Proof. by rewrite !linearB/=. Qed.
Lemma t2linB (M1 M2 : 'End[T1 * T2]) : ⌈ M1; (x1,x2) ⌉ - ⌈ M2; (x1,x2) ⌉ = ⌈ M1 - M2; (x1,x2) ⌉.
Proof. by rewrite !linearB/=. Qed.
Definition tlinB := (t1linB, t2linB).

Lemma t1linZ c (M : 'End[T]) : c *: ⌈ M; x ⌉ = ⌈ c *: M; x ⌉.
Proof. by rewrite !linearZ/=. Qed.
Lemma t2linZ c (M : 'End[T1 * T2]) : c *: ⌈ M; (x1,x2) ⌉ = ⌈ c *: M; (x1,x2) ⌉.
Proof. by rewrite !linearZ/=. Qed.
Definition tlinZ := (t1linZ, t2linZ).

Lemma t1linP c (M1 M2 : 'End[T]) : c *: ⌈ M1; x ⌉ + ⌈ M2; x ⌉ = ⌈ c *: M1 + M2; x ⌉.
Proof. by rewrite !linearP/=. Qed.
Lemma t2linP c (M1 M2 : 'End[T1 * T2]) : c *: ⌈ M1; (x1,x2) ⌉ + ⌈ M2; (x1,x2) ⌉ = ⌈ c *: M1 + M2; (x1,x2) ⌉.
Proof. by rewrite !linearP/=. Qed.
Definition tlinP := (t1linP, t2linP).

Lemma t1linMn n (M : 'End[T]) : ⌈ M; x ⌉ *+ n = ⌈ M *+ n; x ⌉.
Proof. by rewrite !linearMn/=. Qed.
Lemma t2linMn n (M : 'End[T1 * T2]) : ⌈ M *+ n; (x1,x2) ⌉ = ⌈ M *+ n; (x1,x2) ⌉.
Proof. by rewrite !linearMn/=. Qed.
Definition tlinMn := (t1linMn, t2linMn).

Lemma t1linMNn n (M : 'End[T]) : ⌈ M; x ⌉ *- n = ⌈ M *- n; x ⌉.
Proof. by rewrite !linearMNn/=. Qed.
Lemma t2linMNn n (M : 'End[T1 * T2]) : ⌈ M *- n; (x1,x2) ⌉ = ⌈ M *- n; (x1,x2) ⌉.
Proof. by rewrite !linearMNn/=. Qed.
Definition tlinMNn := (t1linMNn, t2linMNn).

Lemma t1lin_sum I (r : seq I) (P : pred I) (F : I -> 'End[T]) :
  \sum_(i <- r | P i) ⌈ F i; x ⌉ = ⌈ \sum_(i <- r | P i) (F i); x ⌉ .
Proof. by rewrite !linear_sum/=. Qed.
Lemma t2lin_sum I (r : seq I) (P : pred I) (F : I -> 'End[T1 * T2]) :
  \sum_(i <- r | P i) ⌈ F i; (x1,x2) ⌉ = ⌈ \sum_(i <- r | P i) (F i); (x1,x2) ⌉ .
Proof. by rewrite !linear_sum/=. Qed.
Definition tlin_sum := (t1lin_sum, t2lin_sum).

Lemma t1lin1 : I_ (lb x) = ⌈ \1; x ⌉.
Proof. by rewrite tf2f1. Qed.
Lemma t2lin1 : I_ (lb x1 :|: lb x2) = ⌈ \1; (x1,x2) ⌉.
Proof. by rewrite tf2f21. Qed.
Definition tlin1 := (t1lin1, t2lin1).

Lemma t1lin_adj (M : 'End[T]) : ⌈ M; x ⌉`A = ⌈ M^A; x ⌉.
Proof. by rewrite lin_adj tf2f_adj. Qed.
Lemma t2lin_adj (M : 'End[T1 * T2]) : ⌈ M; (x1,x2) ⌉`A = ⌈ M^A; (x1,x2) ⌉.
Proof. by rewrite lin_adj tf2f2_adj. Qed.
Definition tlin_adj := (t1lin_adj, t2lin_adj).

Lemma t1lin_conj (M : 'End[T]) : ⌈ M; x ⌉`C = ⌈ M^C; x ⌉.
Proof. by rewrite lin_conj tf2f_conj. Qed.
Lemma t2lin_conj (M : 'End[T1 * T2]) : ⌈ M; (x1,x2) ⌉`C = ⌈ M^C; (x1,x2) ⌉.
Proof. by rewrite lin_conj tf2f2_conj. Qed.
Definition tlin_conj := (t1lin_conj, t2lin_conj).

Lemma t1lin_tr (M : 'End[T]) : ⌈ M; x ⌉`T = ⌈ M^T; x ⌉.
Proof. by rewrite lin_tr tf2f_tr. Qed.
Lemma t2lin_tr (M : 'End[T1 * T2]) : ⌈ M; (x1,x2) ⌉`T = ⌈ M^T; (x1,x2) ⌉.
Proof. by rewrite lin_tr tf2f2_tr. Qed.
Definition tlin_tr := (t1lin_tr, t2lin_tr).

Lemma t1linM (M1 M2 : 'End[T]) : ⌈M1; x⌉ ∗ ⌈M2; x⌉ = ⌈M1 \o M2; x⌉.
Proof. by rewrite linM tf2f_comp. Qed.
Lemma t2linM (M1 M2 : 'End[T1 * T2]) : ⌈M1; (x1,x2)⌉ ∗ ⌈M2; (x1,x2)⌉ = ⌈M1 \o M2; (x1,x2)⌉.
Proof. by rewrite linM tf2f2_comp. Qed.
Definition tlinM := (t1linM, t2linM).

Lemma t1linG (M1 M2 : 'End[T]) : ⌈M1; x⌉ ∘ ⌈M2; x⌉ = ⌈M1 \o M2; x⌉.
Proof. by rewrite linG tf2f_comp. Qed.
Lemma t2linG (M1 M2 : 'End[T1 * T2]) : ⌈M1; (x1,x2)⌉ ∘ ⌈M2; (x1,x2)⌉ = ⌈M1 \o M2; (x1,x2)⌉.
Proof. by rewrite linG tf2f2_comp. Qed.
Definition tlinG := (t1linG, t2linG).

Lemma tlinT (M1 : 'End[T1]) (M2 : 'End[T2]) : ⌈M1; x1⌉ ⊗ ⌈M2; x2⌉ = ⌈M1 ⊗f M2; (x1,x2)⌉.
Proof. by rewrite linT tf2f2_ten. Qed.

Lemma t1lin_ketM (M : 'End[T]) (v : 'Hs T) : ⌈M;x⌉ ∗ ｜v;x〉 = ｜M v;x〉.
Proof. by rewrite lin_ketM tf2f_apply. Qed.
Lemma t2lin_ketM (M : 'End[T1*T2]) (v : 'Hs (T1*T2)) : ⌈M;(x1,x2)⌉ ∗ ｜v;(x1,x2)〉 = ｜M v;(x1,x2)〉.
Proof. by rewrite lin_ketM tf2f2_apply. Qed.
Definition tlin_ketM := (t1lin_ketM, t2lin_ketM).

Lemma t1lin_ketG (M : 'End[T]) (v : 'Hs T) : ⌈M;x⌉ ∘ ｜v;x〉 = ｜M v;x〉.
Proof. by rewrite lin_ketG tf2f_apply. Qed.
Lemma t2lin_ketG (M : 'End[T1*T2]) (v : 'Hs (T1*T2)) : ⌈M;(x1,x2)⌉ ∘ ｜v;(x1,x2)〉 = ｜M v;(x1,x2)〉.
Proof. by rewrite lin_ketG tf2f2_apply. Qed.
Definition tlin_ketG := (t1lin_ketG, t2lin_ketG).
Definition tlin_ket := (tlin_ketM, tlin_ketG).

Lemma t1lin_braM (M : 'End[T]) (v : 'Hs T) : 〈v;x｜ ∗ ⌈M;x⌉ = 〈M^A v;x｜.
Proof. by rewrite lin_braM tf2f_adj tf2f_apply. Qed.
Lemma t2lin_braM (M : 'End[T1*T2]) (v : 'Hs (T1*T2)) : 〈v;(x1,x2)｜ ∗ ⌈M;(x1,x2)⌉ = 〈M^A v;(x1,x2)｜.
Proof. by rewrite lin_braM tf2f2_adj tf2f2_apply. Qed.
Definition tlin_braM := (t1lin_braM, t2lin_braM).

Lemma t1lin_braG (M : 'End[T]) (v : 'Hs T) : 〈v;x｜ ∘ ⌈M;x⌉ = 〈M^A v;x｜.
Proof. by rewrite lin_braG tf2f_adj tf2f_apply. Qed.
Lemma t2lin_braG (M : 'End[T1*T2]) (v : 'Hs (T1*T2)) : 〈v;(x1,x2)｜ ∘ ⌈M;(x1,x2)⌉ = 〈M^A v;(x1,x2)｜.
Proof. by rewrite lin_braG tf2f2_adj tf2f2_apply. Qed.
Definition tlin_braG := (t1lin_braG, t2lin_braG).
Definition tlin_bra := (tlin_braM, tlin_braG).

Lemma t1ket0 : ｜0; x〉 = 0.
Proof. by rewrite !linear0/=. Qed.
Lemma t2ket0 : ｜0; (x1,x2)〉 = 0.
Proof. by rewrite !linear0/=. Qed.
Definition tket0 := (t1ket0, t2ket0).

Lemma t1ketN (v : 'Hs T) : - ｜v; x〉 = ｜- v; x〉.
Proof. by rewrite !linearN/=. Qed.
Lemma t2ketN (v : 'Hs (T1 * T2)) : - ｜v; (x1,x2)〉 = ｜- v; (x1,x2)〉.
Proof. by rewrite !linearN/=. Qed.
Definition tketN := (t1ketN, t2ketN).

Lemma t1ketD (v1 v2 : 'Hs T) : ｜v1; x〉 + ｜v2; x〉 = ｜v1 + v2; x〉.
Proof. by rewrite !linearD/=. Qed.
Lemma t2ketD (v1 v2 : 'Hs (T1 * T2)) : ｜v1; (x1,x2)〉 + ｜v2; (x1,x2)〉 = ｜v1 + v2; (x1,x2)〉.
Proof. by rewrite !linearD/=. Qed.
Definition tketD := (t1ketD, t2ketD).

Lemma t1ketB (v1 v2 : 'Hs T) : ｜v1; x〉 - ｜v2; x〉 = ｜v1 - v2; x〉.
Proof. by rewrite !linearB/=. Qed.
Lemma t2ketB (v1 v2 : 'Hs (T1 * T2)) : ｜v1; (x1,x2)〉 - ｜v2; (x1,x2)〉 = ｜v1 - v2; (x1,x2)〉.
Proof. by rewrite !linearB/=. Qed.
Definition tketB := (t1ketB, t2ketB).

Lemma t1ketZ c (v : 'Hs T) : c *: ｜v; x〉 = ｜c *: v; x〉.
Proof. by rewrite !linearZ/=. Qed.
Lemma t2ketZ c (v : 'Hs (T1 * T2)) : c *: ｜v; (x1,x2)〉 = ｜c *: v; (x1,x2)〉.
Proof. by rewrite !linearZ/=. Qed.
Definition tketZ := (t1ketZ, t2ketZ).

Lemma t1ketP c (v1 v2 : 'Hs T) : c *: ｜v1; x〉 + ｜v2; x〉 = ｜c *: v1 + v2; x〉.
Proof. by rewrite !linearP/=. Qed.
Lemma t2ketP c (v1 v2 : 'Hs (T1 * T2)) : c *: ｜v1; (x1,x2)〉 + ｜v2; (x1,x2)〉 = ｜c *: v1 + v2; (x1,x2)〉.
Proof. by rewrite !linearP/=. Qed.
Definition tketP := (t1ketP, t2ketP).

Lemma t1ketMn n (v : 'Hs T) : ｜v; x〉 *+ n = ｜v *+ n; x〉.
Proof. by rewrite !linearMn/=. Qed.
Lemma t2ketMn n (v : 'Hs (T1 * T2)) : ｜v *+ n; (x1,x2)〉 = ｜v *+ n; (x1,x2)〉.
Proof. by rewrite !linearMn/=. Qed.
Definition tketMn := (t1ketMn, t2ketMn).

Lemma t1ketMNn n (v : 'Hs T) : ｜v; x〉 *- n = ｜v *- n; x〉.
Proof. by rewrite !linearMNn/=. Qed.
Lemma t2ketMNn n (v : 'Hs (T1 * T2)) : ｜v *- n; (x1,x2)〉 = ｜v *- n; (x1,x2)〉.
Proof. by rewrite !linearMNn/=. Qed.
Definition tketMNn := (t1ketMNn, t2ketMNn).

Lemma t1ket_sum I (r : seq I) (P : pred I) (F : I -> 'Hs T) :
  \sum_(i <- r | P i) ｜F i; x〉 = ｜\sum_(i <- r | P i) (F i); x〉 .
Proof. by rewrite !linear_sum/=. Qed.
Lemma t2ket_sum I (r : seq I) (P : pred I) (F : I -> 'Hs (T1 * T2)) :
  \sum_(i <- r | P i) ｜F i; (x1,x2)〉 = ｜\sum_(i <- r | P i) (F i); (x1,x2)〉 .
Proof. by rewrite !linear_sum/=. Qed.
Definition tket_sum := (t1ket_sum, t2ket_sum).

Lemma t1ket_adj (v : 'Hs T) : ｜v; x〉`A = 〈v; x｜.
Proof. by rewrite ket_adj. Qed.
Lemma t2ket_adj (v : 'Hs (T1 * T2)) : ｜v; (x1,x2)〉`A = 〈v; (x1,x2)｜.
Proof. by rewrite ket_adj. Qed.
Definition tket_adj := (t1ket_adj, t2ket_adj).

Lemma t1ket_conj (v : 'Hs T) : ｜v; x〉`C = ｜v^*v; x〉.
Proof. by rewrite ket_conj tv2v_conj. Qed.
Lemma t2ket_conj (v : 'Hs (T1 * T2)) : ｜v; (x1,x2)〉`C = ｜v^*v; (x1,x2)〉.
Proof. by rewrite ket_conj tv2v2_conj. Qed.
Definition tket_conj := (t1ket_conj, t2ket_conj).

Lemma t1ket_tr (v : 'Hs T) : ｜v; x〉`T = 〈v^*v; x｜.
Proof. by rewrite ket_tr tv2v_conj. Qed.
Lemma t2ket_tr (v : 'Hs (T1 * T2)) : ｜v; (x1,x2)〉`T = 〈v^*v; (x1,x2)｜.
Proof. by rewrite ket_tr tv2v2_conj. Qed.
Definition tket_tr := (t1ket_tr, t2ket_tr).

Lemma tketT (v1 : 'Hs T1) (v2 : 'Hs T2) : ｜v1; x1〉 ⊗ ｜v2; x2〉 = ｜v1 ⊗t v2; (x1,x2)〉.
Proof. by rewrite ketT tv2v2_ten. Qed.

Lemma t1bra0 : 〈0; x｜ = 0.
Proof. by rewrite !linear0/=. Qed.
Lemma t2bra0 : 〈0; (x1,x2)｜ = 0.
Proof. by rewrite !linear0/=. Qed.
Definition tbra0 := (t1bra0, t2bra0).

Lemma t1braN (v : 'Hs T) : - 〈v; x｜ = 〈- v; x｜.
Proof. by rewrite !linearN/=. Qed.
Lemma t2braN (v : 'Hs (T1 * T2)) : - 〈v; (x1,x2)｜ = 〈- v; (x1,x2)｜.
Proof. by rewrite !linearN/=. Qed.
Definition tbraN := (t1braN, t2braN).

Lemma t1braD (v1 v2 : 'Hs T) : 〈v1; x｜ + 〈v2; x｜ = 〈v1 + v2; x｜.
Proof. by rewrite !linearD/=. Qed.
Lemma t2braD (v1 v2 : 'Hs (T1 * T2)) : 〈v1; (x1,x2)｜ + 〈v2; (x1,x2)｜ = 〈v1 + v2; (x1,x2)｜.
Proof. by rewrite !linearD/=. Qed.
Definition tbraD := (t1braD, t2braD).

Lemma t1braB (v1 v2 : 'Hs T) : 〈v1; x｜ - 〈v2; x｜ = 〈v1 - v2; x｜.
Proof. by rewrite !linearB/=. Qed.
Lemma t2braB (v1 v2 : 'Hs (T1 * T2)) : 〈v1; (x1,x2)｜ - 〈v2; (x1,x2)｜ = 〈v1 - v2; (x1,x2)｜.
Proof. by rewrite !linearB/=. Qed.
Definition tbraB := (t1braB, t2braB).

Lemma t1braZ c (v : 'Hs T) : c *: 〈v; x｜ = 〈c^* *: v; x｜.
Proof. by rewrite !linearZ/= conjCK. Qed.
Lemma t2braZ c (v : 'Hs (T1 * T2)) : c *: 〈v; (x1,x2)｜ = 〈c^* *: v; (x1,x2)｜.
Proof. by rewrite !linearZ/= conjCK. Qed.
Definition tbraZ := (t1braZ, t2braZ).

Lemma t1braP c (v1 v2 : 'Hs T) : c *: 〈v1; x｜ + 〈v2; x｜ = 〈c^* *: v1 + v2; x｜.
Proof. by rewrite !linearP/= conjCK. Qed.
Lemma t2braP c (v1 v2 : 'Hs (T1 * T2)) : c *: 〈v1; (x1,x2)｜ + 〈v2; (x1,x2)｜ = 〈c^* *: v1 + v2; (x1,x2)｜.
Proof. by rewrite !linearP/= conjCK. Qed.
Definition tbraP := (t1braP, t2braP).

Lemma t1braMn n (v : 'Hs T) : 〈v; x｜ *+ n = 〈v *+ n; x｜.
Proof. by rewrite !linearMn/=. Qed.
Lemma t2braMn n (v : 'Hs (T1 * T2)) : 〈v *+ n; (x1,x2)｜ = 〈v *+ n; (x1,x2)｜.
Proof. by rewrite !linearMn/=. Qed.
Definition tbraMn := (t1braMn, t2braMn).

Lemma t1braMNn n (v : 'Hs T) : 〈v; x｜ *- n = 〈v *- n; x｜.
Proof. by rewrite !linearMNn/=. Qed.
Lemma t2braMNn n (v : 'Hs (T1 * T2)) : 〈v *- n; (x1,x2)｜ = 〈v *- n; (x1,x2)｜.
Proof. by rewrite !linearMNn/=. Qed.
Definition tbraMNn := (t1braMNn, t2braMNn).

Lemma t1bra_sum I (r : seq I) (P : pred I) (F : I -> 'Hs T) :
  \sum_(i <- r | P i) 〈F i; x｜ = 〈\sum_(i <- r | P i) (F i); x｜ .
Proof. by rewrite !linear_sum/=. Qed.
Lemma t2bra_sum I (r : seq I) (P : pred I) (F : I -> 'Hs (T1 * T2)) :
  \sum_(i <- r | P i) 〈F i; (x1,x2)｜ = 〈\sum_(i <- r | P i) (F i); (x1,x2)｜ .
Proof. by rewrite !linear_sum/=. Qed.
Definition tbra_sum := (t1bra_sum, t2bra_sum).

Lemma t1bra_adj (v : 'Hs T) : 〈v; x｜`A = ｜v; x〉.
Proof. by rewrite bra_adj. Qed.
Lemma t2bra_adj (v : 'Hs (T1 * T2)) : 〈v; (x1,x2)｜`A = ｜v; (x1,x2)〉.
Proof. by rewrite bra_adj. Qed.
Definition tbra_adj := (t1bra_adj, t2bra_adj).

Lemma t1bra_conj (v : 'Hs T) : 〈v; x｜`C = 〈v^*v; x｜.
Proof. by rewrite bra_conj tv2v_conj. Qed.
Lemma t2bra_conj (v : 'Hs (T1 * T2)) : 〈v; (x1,x2)｜`C = 〈v^*v; (x1,x2)｜.
Proof. by rewrite bra_conj tv2v2_conj. Qed.
Definition tbra_conj := (t1bra_conj, t2bra_conj).

Lemma t1bra_tr (v : 'Hs T) : 〈v; x｜`T = ｜v^*v; x〉.
Proof. by rewrite bra_tr tv2v_conj. Qed.
Lemma t2bra_tr (v : 'Hs (T1 * T2)) : 〈v; (x1,x2)｜`T = ｜v^*v; (x1,x2)〉.
Proof. by rewrite bra_tr tv2v2_conj. Qed.
Definition tbra_tr := (t1bra_tr, t2bra_tr).

Lemma tbraT (v1 : 'Hs T1) (v2 : 'Hs T2) : 〈v1; x1｜ ⊗ 〈v2; x2｜ = 〈v1 ⊗t v2; (x1,x2)｜.
Proof. by rewrite braT tv2v2_ten. Qed.

Lemma t1innerM (u v : 'Hs T) : 〈u;x｜ ∗ ｜v;x〉 = [<u ; v>]%:QE.
Proof. by rewrite innerM tv2v_dot. Qed.
Lemma t2innerM (u v : 'Hs (T1 * T2)) : 〈u;(x1,x2)｜ ∗ ｜v;(x1,x2)〉 = [<u ; v>]%:QE.
Proof. by rewrite innerM tv2v2_dot. Qed.
Lemma t1innerG (u v : 'Hs T) : 〈u;x｜ ∘ ｜v;x〉 = [<u ; v>]%:QE.
Proof. by rewrite innerG tv2v_dot. Qed.
Lemma t2innerG (u v : 'Hs (T1 * T2)) : 〈u;(x1,x2)｜ ∘ ｜v;(x1,x2)〉 = [<u ; v>]%:QE.
Proof. by rewrite innerG tv2v2_dot. Qed.
Definition tinnerM := (t1innerM, t2innerM).
Definition tinnerG := (t1innerG, t2innerG).
Definition tinner := (tinnerM, tinnerG).
Lemma t1outerM (u v : 'Hs T) : ｜v;x〉 ∗ 〈u;x｜ = ⌈ [> v ; u <]; x ⌉.
Proof. by rewrite outerM tv2v_out. Qed.
Lemma t2outerM (u v : 'Hs (T1 * T2)) : ｜v;(x1,x2)〉 ∗ 〈u;(x1,x2)｜ = ⌈ [> v ; u <]; (x1,x2) ⌉.
Proof. by rewrite outerM tv2v2_out. Qed.
Lemma t1outerG (u v : 'Hs T) : ｜v;x〉 ∘ 〈u;x｜ = ⌈ [> v ; u <]; x ⌉.
Proof. by rewrite outerG tv2v_out. Qed.
Lemma t2outerG (u v : 'Hs (T1 * T2)) : ｜v;(x1,x2)〉 ∘ 〈u;(x1,x2)｜ = ⌈ [> v ; u <]; (x1,x2) ⌉.
Proof. by rewrite outerG tv2v2_out. Qed.
Definition touterM := (t1outerM, t2outerM).
Definition touterG := (t1outerG, t2outerG).
Definition touter := (touterM, touterG).

Lemma tlinTC (M1 : 'End[T1]) (M2 : 'End[T2]) : ⌈M1 ⊗f M2; (x1,x2)⌉ = ⌈M2 ⊗f M1; (x2,x1)⌉.
Proof. by rewrite -tlinT tenqC linT tf2f2_ten. Qed.
Lemma tketTC (v1 : 'Hs T1) (v2 : 'Hs T2) : ｜v1 ⊗t v2; (x1,x2)〉 = ｜v2 ⊗t v1; (x2,x1)〉.
Proof. by rewrite -tketT tenqC ketT tv2v2_ten. Qed.
Lemma tbraTC (v1 : 'Hs T1) (v2 : 'Hs T2) : 〈v1 ⊗t v2; (x1,x2)｜ = 〈v2 ⊗t v1; (x2,x1)｜.
Proof. by rewrite -tbraT tenqC braT tv2v2_ten. Qed.

Lemma tketT_swap (u : 'Hs (T1 * T2)) :
  ｜(swaptf u) ; (x2,x1) 〉 = ｜u ; (x1,x2) 〉.
Proof.
rewrite (onb_vec t2tv2_onbasis u) !linear_sum/=; apply eq_bigr=>i _.
by rewrite !linearZ/=; f_equal; rewrite /tentv_fun swaptfEtv tketTC.
Qed.

Lemma tbraT_swap (u : 'Hs (T1 * T2)) :
  〈(swaptf u) ; (x2,x1) ｜ = 〈u ; (x1,x2) ｜.
Proof.
rewrite (onb_vec t2tv2_onbasis u) !linear_sum/=; apply eq_bigr=>i _.
by rewrite !linearZ/=; f_equal; rewrite /tentv_fun swaptfEtv tbraTC.
Qed.

Lemma tlinT_swap (M : 'End[T1 * T2]) :
  ⌈ swaptf \o M \o swaptf ; (x2,x1) ⌉ = ⌈ M ; (x1,x2) ⌉.
Proof.
rewrite (onb_lfun2id t2tv2_onbasis M) pair_big/= linear_sumr linear_suml !linear_sum/=.
apply eq_bigr=>i _; rewrite linearZr linearZl/= !linearZ/=; f_equal.
by rewrite /tentv_fun swaptf_out !swaptfEtv -!tentv_out tlinTC.
Qed.

Lemma touterT_swap (u v : 'Hs (T1 * T2)) :
  ⌈ [> swaptf u ; swaptf v <] ; (x2,x1) ⌉ = ⌈ [> u ; v <] ; (x1,x2) ⌉.
Proof. by rewrite -tlinT_swap swaptf_out. Qed.

Section tlinG.
Variable (N1 : 'End[T1]) (N2 : 'End[T2]) (M : 'End[T1 * T2]) (v : 'Hs (T1 * T2)).

Lemma tlin1Gl : ⌈\1;x1⌉ ∘ ⌈M; (x1,x2)⌉ = ⌈M; (x1,x2)⌉.
Proof. by rewrite -tf2f1 dotIqid// subsetUl. Qed.
Lemma tlin1Gr : ⌈\1;x2⌉ ∘ ⌈M; (x1,x2)⌉ = ⌈M; (x1,x2)⌉.
Proof. by rewrite -tf2f1 dotIqid// subsetUr. Qed.
Lemma tlinG1l : ⌈M; (x1,x2)⌉ ∘ ⌈\1;x1⌉ = ⌈M; (x1,x2)⌉.
Proof. by rewrite -tf2f1 dotqIid// subsetUl. Qed.
Lemma tlinG1r : ⌈M; (x1,x2)⌉ ∘ ⌈\1;x2⌉ = ⌈M; (x1,x2)⌉.
Proof. by rewrite -tf2f1 dotqIid// subsetUr. Qed.
Definition tlin1G := (tlin1Gl, tlin1Gr).
Definition tlinG1 := (tlinG1l, tlinG1r).
Lemma tket1Gl : ⌈\1;x1⌉ ∘ ｜v; (x1,x2)〉 = ｜v; (x1,x2)〉.
Proof. by rewrite -tf2f1 dotIqid// subsetUl. Qed.
Lemma tket1Gr : ⌈\1;x2⌉ ∘ ｜v; (x1,x2)〉 = ｜v; (x1,x2)〉.
Proof. by rewrite -tf2f1 dotIqid// subsetUr. Qed.
Definition tket1G := (tket1Gl, tket1Gr).
Lemma tbra1Gl : 〈v; (x1,x2)｜ ∘ ⌈\1;x1⌉ = 〈v; (x1,x2)｜.
Proof. by rewrite -tf2f1 dotqIid// subsetUl. Qed.
Lemma tbra1Gr : 〈v; (x1,x2)｜ ∘ ⌈\1;x2⌉ = 〈v; (x1,x2)｜.
Proof. by rewrite -tf2f1 dotqIid// subsetUr. Qed.
Definition tbraG1 := (tbra1Gl, tbra1Gr).

Lemma tlintGl : ⌈N1;x1⌉ ∘ ⌈M; (x1,x2)⌉ = ⌈(N1 ⊗f \1) \o M; (x1,x2)⌉.
Proof. 
by rewrite -[RHS]tlinG -[X in _ = X ∘ _]tlinT -tf2f1 
  -dotq_ten/= -?dotqA/= ?dotIqid// ?subsetUr// -disjoint_neqE.
Qed.
Lemma tlintGr : ⌈N2;x2⌉ ∘ ⌈M; (x1,x2)⌉ = ⌈(\1 ⊗f N2) \o M; (x1,x2)⌉.
Proof.
by rewrite -[RHS]tlinG -[X in _ = X ∘ _]tlinT -tf2f1 tenqC 
  -dotq_ten/= -?dotqA/= ?dotIqid// ?subsetUl// disjoint_sym.
Qed.
Lemma tlinGtl : ⌈M; (x1,x2)⌉ ∘ ⌈N1;x1⌉ = ⌈M \o (N1 ⊗f \1); (x1,x2)⌉.
Proof.
by rewrite -[RHS]tlinG -[X in _ = _ ∘ X]tlinT -tf2f1 tenqC
  -dotq_ten/= ?dotqA/= ?dotqIid// ?subsetUr// disjoint_sym.
Qed.
Lemma tlinGtr : ⌈M; (x1,x2)⌉ ∘ ⌈N2;x2⌉ = ⌈M \o (\1 ⊗f N2); (x1,x2)⌉.
Proof.
by rewrite -[RHS]tlinG -[X in _ = _ ∘ X]tlinT -tf2f1
  -dotq_ten/= ?dotqA/= ?dotqIid// ?subsetUl.
Qed.
Lemma tketGl : ⌈N1;x1⌉ ∘ ｜v; (x1,x2)〉 = ｜(N1 ⊗f \1) v; (x1,x2)〉.
Proof. 
by rewrite -[RHS]tlin_ketG -[X in _ = X ∘ _]tlinT -tf2f1 
  -dotq_ten/= -?dotqA/= ?dotIqid// ?subsetUr.
Qed.
Lemma tketGr : ⌈N2;x2⌉ ∘ ｜v; (x1,x2)〉 = ｜(\1 ⊗f N2) v; (x1,x2)〉.
Proof.
by rewrite -[RHS]tlin_ketG -[X in _ = X ∘ _]tlinT -tf2f1 tenqC 
  -dotq_ten/= -?dotqA/= ?dotIqid// ?subsetUl// disjoint_sym.
Qed.
Lemma tbraGl : 〈v; (x1,x2)｜ ∘ ⌈N1;x1⌉ = 〈(N1^A ⊗f \1) v; (x1,x2)｜.
Proof.
by rewrite -adjf1 -tentf_adj -[RHS]tlin_braG -[X in _ = _ ∘ X]tlinT tenqC -tf2f1
  -dotq_ten/= ?dotqA/= ?dotqIid// ?subsetUr// disjoint_sym.
Qed.
Lemma tbraGr : 〈v; (x1,x2)｜ ∘ ⌈N2;x2⌉ = 〈(\1 ⊗f N2^A) v; (x1,x2)｜.
Proof.
by rewrite -adjf1 -tentf_adj -[RHS]tlin_braG -[X in _ = _ ∘ X]tlinT -tf2f1
  -dotq_ten/= ?dotqA/= ?dotqIid// ?subsetUl.
Qed.
End tlinG.

Section tlinTcomT.
Variable (M M1 M2 : 'End[T]) (N N1 N2 : 'End[T1 * T2]).
Variable (v : 'Hs T) (u : 'Hs (T1 * T2)) (S S' : {set L}) (e : {wf H | S,S'}).

Lemma t1lin_comTll : [disjoint lb x & S'] ->
  ⌈ M1; x ⌉ ∘ (⌈ M2; x ⌉ ⊗ e) = ⌈ M1 \o M2; x ⌉ ⊗ e.
Proof. by move=>P; rewrite lin_comTll// tf2f_comp. Qed.
Lemma t2lin_comTll : [disjoint lb x1 :|: lb x2 & S'] ->
  ⌈ N1; (x1,x2) ⌉ ∘ (⌈ N2; (x1,x2) ⌉ ⊗ e) = ⌈ N1 \o N2; (x1,x2) ⌉ ⊗ e.
Proof. by move=>P; rewrite lin_comTll// tf2f2_comp. Qed.
Definition tlin_comTll := (t1lin_comTll, t2lin_comTll).

Lemma t1lin_comTlr : [disjoint lb x & S'] ->
  ⌈ M1; x ⌉ ∘ (e ⊗ ⌈ M2; x ⌉) = e ⊗ ⌈ M1 \o M2; x ⌉.
Proof. by move=>P; rewrite lin_comTlr// tf2f_comp. Qed.
Lemma t2lin_comTlr : [disjoint lb x1 :|: lb x2 & S'] ->
  ⌈ N1; (x1,x2) ⌉ ∘ (e ⊗ ⌈ N2; (x1,x2) ⌉) = e ⊗ ⌈ N1 \o N2; (x1,x2) ⌉.
Proof. by move=>P; rewrite lin_comTlr// tf2f2_comp. Qed.
Definition tlin_comTlr := (t1lin_comTll, t2lin_comTll).

Lemma t1lin_comTrl : [disjoint lb x & S] ->
  (⌈ M1; x ⌉ ⊗ e) ∘ ⌈ M2; x ⌉ = ⌈ M1 \o M2; x ⌉ ⊗ e.
Proof. by move=>P; rewrite lin_comTrl// tf2f_comp. Qed.
Lemma t2lin_comTrl : [disjoint lb x1 :|: lb x2 & S] ->
  (⌈ N1; (x1,x2) ⌉ ⊗ e) ∘ ⌈ N2; (x1,x2) ⌉ = ⌈ N1 \o N2; (x1,x2) ⌉ ⊗ e.
Proof. by move=>P; rewrite lin_comTrl// tf2f2_comp. Qed.
Definition tlin_comTrl := (t1lin_comTrl, t2lin_comTrl).

Lemma t1lin_comTrr : [disjoint lb x & S] ->
  (e ⊗ ⌈ M1; x ⌉) ∘ ⌈ M2; x ⌉ = e ⊗ ⌈ M1 \o M2; x ⌉.
Proof. by move=>P; rewrite lin_comTrr// tf2f_comp. Qed.
Lemma t2lin_comTrr : [disjoint lb x1 :|: lb x2 & S] ->
  (e ⊗ ⌈ N1; (x1,x2) ⌉) ∘ ⌈ N2; (x1,x2) ⌉ = e ⊗ ⌈ N1 \o N2; (x1,x2) ⌉.
Proof. by move=>P; rewrite lin_comTrr// tf2f2_comp. Qed.
Definition tlin_comTrr := (t1lin_comTrr, t2lin_comTrr).
Definition tlin_comT := (tlin_comTll, tlin_comTlr, tlin_comTrl, tlin_comTrr).

Lemma t1lin_ketTl : [disjoint lb x & S'] ->
  ⌈ M; x ⌉ ∘ (｜v;x〉 ⊗ e) = ｜M v;x〉 ⊗ e.
Proof. by move=>P; rewrite lin_ketTl// tf2f_apply. Qed.
Lemma t2lin_ketTl : [disjoint lb x1 :|: lb x2 & S'] ->
  ⌈ N; (x1,x2) ⌉ ∘ (｜u; (x1,x2)〉 ⊗ e) = ｜N u; (x1,x2)〉 ⊗ e.
Proof. by move=>P; rewrite lin_ketTl// tf2f2_apply. Qed.
Definition tlin_ketTl := (t1lin_ketTl, t2lin_ketTl).

Lemma t1lin_ketTr : [disjoint lb x & S'] ->
  ⌈ M; x ⌉ ∘ (e ⊗ ｜v;x〉) = e ⊗ ｜M v;x〉.
Proof. by move=>P; rewrite lin_ketTr// tf2f_apply. Qed.
Lemma t2lin_ketTr : [disjoint lb x1 :|: lb x2 & S'] ->
  ⌈ N; (x1,x2) ⌉ ∘ (e ⊗ ｜u; (x1,x2)〉) = e ⊗ ｜N u; (x1,x2)〉.
Proof. by move=>P; rewrite lin_ketTr// tf2f2_apply. Qed.
Definition tlin_ketTr := (t1lin_ketTr, t2lin_ketTr).
Definition tlin_ketT := (tlin_ketTl, tlin_ketTr).

Lemma t1linT_ketl : [disjoint lb x & S] ->
  (⌈ M; x ⌉ ⊗ e) ∘ ｜v;x〉 = ｜M v;x〉 ⊗ e.
Proof. by move=>P; rewrite dotqTrl//= tlin_ketG. Qed.
Lemma t2linT_ketl : [disjoint lb x1 :|: lb x2 & S] ->
  (⌈ N; (x1,x2) ⌉ ⊗ e) ∘ ｜u; (x1,x2)〉 = ｜N u; (x1,x2)〉 ⊗ e.
Proof. by move=>P; rewrite dotqTrl//= tlin_ketG. Qed.
Definition tlinT_ketl := (t1linT_ketl, t2linT_ketl).

Lemma t1linT_ketr : [disjoint lb x & S] ->
  (e ⊗ ⌈ M; x ⌉) ∘ ｜v;x〉 = e ⊗ ｜M v;x〉.
Proof. by move=>P; rewrite dotqTrr//= tlin_ketG. Qed.
Lemma t2linT_ketr : [disjoint lb x1 :|: lb x2 & S] ->
  (e ⊗ ⌈ N; (x1,x2) ⌉) ∘ ｜u; (x1,x2)〉 = e ⊗ ｜N u; (x1,x2)〉.
Proof. by move=>P; rewrite dotqTrr//= tlin_ketG. Qed.
Definition tlinT_ketr := (t1linT_ketr, t2linT_ketr).
Definition tlinT_ket := (tlinT_ketl, tlinT_ketr).

Lemma t1lin_braTl : [disjoint lb x & S] ->
  (〈v; x｜ ⊗ e) ∘ ⌈ M; x ⌉ = 〈M^A v; x｜ ⊗ e.
Proof. by move=>P; rewrite lin_braTl// tf2f_adj tf2f_apply. Qed.
Lemma t2lin_braTl : [disjoint lb x1 :|: lb x2 & S] ->
  (〈u; (x1,x2)｜ ⊗ e) ∘ ⌈ N; (x1,x2) ⌉ = 〈N^A u; (x1,x2)｜ ⊗ e.
Proof. by move=>P; rewrite lin_braTl// tf2f2_adj tf2f2_apply. Qed.
Definition tlin_braTl := (t1lin_braTl, t2lin_braTl).

Lemma t1lin_braTr : [disjoint lb x & S] ->
  (e ⊗ 〈v; x｜) ∘ ⌈ M; x ⌉ = e ⊗ 〈M^A v; x｜.
Proof. by move=>P; rewrite lin_braTr// tf2f_adj tf2f_apply. Qed.
Lemma t2lin_braTr : [disjoint lb x1 :|: lb x2 & S] ->
  (e ⊗ 〈u; (x1,x2)｜) ∘ ⌈ N; (x1,x2) ⌉ = e ⊗ 〈N^A u; (x1,x2)｜.
Proof. by move=>P; rewrite lin_braTr// tf2f2_adj tf2f2_apply. Qed.
Definition tlin_braTr := (t1lin_braTr, t2lin_braTr).
Definition tlin_braT := (tlin_braTl, tlin_braTr).

Lemma t1linT_bral : [disjoint lb x & S'] ->
  〈v; x｜ ∘ (⌈ M; x ⌉ ⊗ e) = 〈M^A v; x｜ ⊗ e.
Proof. by move=>P; rewrite dotqTll//= tlin_braG. Qed.
Lemma t2linT_bral : [disjoint lb x1 :|: lb x2 & S'] ->
  〈u; (x1,x2)｜ ∘ (⌈ N; (x1,x2) ⌉ ⊗ e) = 〈N^A u; (x1,x2)｜ ⊗ e.
Proof. by move=>P; rewrite dotqTll//= tlin_braG. Qed.
Definition tlinT_bral := (t1linT_bral, t2linT_bral).

Lemma t1linT_brar : [disjoint lb x & S'] ->
  〈v; x｜ ∘ (e ⊗ ⌈ M; x ⌉) = e ⊗ 〈M^A v; x｜.
Proof. by move=>P; rewrite dotqTlr//= tlin_braG. Qed.
Lemma t2linT_brar : [disjoint lb x1 :|: lb x2 & S'] ->
  〈u; (x1,x2)｜ ∘ (e ⊗ ⌈ N; (x1,x2) ⌉) = e ⊗ 〈N^A u; (x1,x2)｜.
Proof. by move=>P; rewrite dotqTlr//= tlin_braG. Qed.
Definition tlinT_brar := (t1linT_brar, t2linT_brar).
Definition tlinT_bra := (tlinT_bral, tlinT_brar).

End tlinTcomT.

Section ketBT.
Variable (I : Type) (r : seq I) (P : pred I) (d : I -> vars T) (F G : I -> 'Hs T).
Definition tketBT_adj := @ketBT_adj.
Definition tbraBT_adj := @braBT_adj.
Lemma tketBT_tr : (\tens_(i <- r | P i) ｜F i;d i〉)`T = \tens_(i <- r | P i) 〈(F i)^*v;d i｜.
Proof. by rewrite ketBT_tr; under eq_bigr do rewrite tv2v_conj. Qed.
Lemma tketBT_conj : (\tens_(i <- r | P i) ｜F i;d i〉)`C = \tens_(i <- r | P i) ｜(F i)^*v;d i〉.
Proof. by rewrite ketBT_conj; under eq_bigr do rewrite tv2v_conj. Qed.
Lemma tbraBT_tr : (\tens_(i <- r | P i) 〈F i;d i｜)`T = \tens_(i <- r | P i) ｜(F i)^*v;d i〉.
Proof. by rewrite braBT_tr; under eq_bigr do rewrite tv2v_conj. Qed.
Lemma tbraBT_conj : (\tens_(i <- r | P i) 〈F i;d i｜)`C = \tens_(i <- r | P i) 〈(F i)^*v;d i｜.
Proof. by rewrite braBT_conj; under eq_bigr do rewrite tv2v_conj. Qed.
Lemma touterMBT : (\tens_(i <- r | P i) ｜F i;d i〉) ∗ (\tens_(i <- r | P i) 〈G i;d i｜) 
  = \tens_(i <- r | P i) (⌈[>F i; G i<]; d i⌉).
Proof. by rewrite outerMBT; under eq_bigr do rewrite outerM tv2v_out. Qed.
Lemma touterGBT : (\tens_(i <- r | P i) ｜F i;d i〉) ∘ (\tens_(i <- r | P i) 〈G i;d i｜) 
  = \tens_(i <- r | P i) (⌈[>F i; G i<]; d i⌉).
Proof. by rewrite dotq_com/= touterMBT. Qed.
End ketBT.

Lemma tinnerMBT (I : finType) (P : pred I) (d : I -> vars T) (F G : I -> 'Hs T) : 
  (forall i j : I, P i -> P j -> i != j -> [disjoint lb (d i) & lb (d j)]) ->
  (\tens_(i | P i) 〈F i;d i｜) ∗ (\tens_(i | P i) ｜G i;d i〉) 
  = (\prod_(i | P i) [<F i ; G i>])%:QE.
Proof.
move=>P1; rewrite innerMBT ?index_enum_uniq=>[i j Pi Pj nij|//|].
by rewrite P1. by under eq_bigr do rewrite tv2v_dot.
Qed.

Lemma tinnerGBT (I : finType) (P : pred I) (d : I -> vars T) (F G : I -> 'Hs T) : 
  (forall i j : I, P i -> P j -> i != j -> [disjoint lb (d i) & lb (d j)]) ->
  (\tens_(i | P i) 〈F i;d i｜) ∘ (\tens_(i | P i) ｜G i;d i〉) 
  = (\prod_(i | P i) [<F i ; G i>])%:QE.
Proof. rewrite dotq_com/=; exact: tinnerMBT. Qed.
End QExprExtra.


Section PackingQExpr.
Variable (L : finType) (H : L -> chsType).
Notation vars T := (@tvars_of L H _ (Phant T)).
Implicit Type (T : ihbFinType).
(* tensor for tuples, ffun, dffun *)
(* since tensor changes the type, we are not able to use bigop instead *)

Section pvars2.
Variable (T1 T2 : ihbFinType) (x : vars T1) (y : vars T2) (dis : [disjoint lb x & lb y]).

Lemma pvars2Ev (u : 'Hs (T1 * T2)) : ｜u ; pvars2 dis〉 = ｜u; (x,y)〉.
Proof. by rewrite tv2v2_pvars2. Qed.  

Lemma pvars2Ef (u : 'End[T1 * T2]) : ⌈ u ; pvars2 dis ⌉ = ⌈ u ; (x,y) ⌉.
Proof. by rewrite tf2f2_pvars2. Qed.

Definition pvars2E := (pvars2Ev, pvars2Ef).
End pvars2.

Section pvars_tuple.
Variable (T : ihbFinType) (n : nat) (x : n.-tuple (vars T)).
Variable (dis : forall i j, i != j -> [disjoint lb (x ~_ i) & lb (x ~_ j)]).

Lemma pvars_tupleEt (t : n.-tuple T) :
  ｜''t; pvars_tuple dis〉 = \tens_i ｜''(t ~_ i); x ~_ i〉.
Proof. by rewrite pvars_t2tv tenvm_correct. Qed.

Lemma pvars_tupleEv (v : n.-tuple 'Hs T) :
  ｜tentv_tuple v; pvars_tuple dis〉 = \tens_i ｜v ~_ i; x ~_ i〉.
Proof. by rewrite pvars_tentv tenvm_correct. Qed.

Lemma pvars_tupleEf (v : n.-tuple 'End[T]) :
  ⌈ tentf_tuple v ; pvars_tuple dis ⌉ = \tens_i ⌈ v ~_ i ; x ~_ i ⌉.
Proof. by rewrite pvars_tentf tenfm_correct. Qed.

Lemma pvarsEt_nseq (t : T) :
  ｜''(nseq_tuple n t); pvars_tuple dis〉 = \tens_i ｜''t; x ~_ i〉.
Proof. by rewrite pvars_tupleEt; under eq_bigr do rewrite tnth_nseq. Qed.

Lemma pvarsEv_nseq (v : 'Hs T) :
  ｜tentv_tuple (nseq_tuple n v); pvars_tuple dis〉 = \tens_i ｜v; x ~_ i〉.
Proof. by rewrite pvars_tupleEv; under eq_bigr do rewrite tnth_nseq. Qed.

Lemma pvarsEf_nseq (v : 'End[T]) :
  ⌈ tentf_tuple (nseq_tuple n v) ; pvars_tuple dis ⌉ = \tens_i ⌈ v ; x ~_ i ⌉.
Proof. by rewrite pvars_tupleEf; under eq_bigr do rewrite tnth_nseq. Qed.
End pvars_tuple.

Section pvars_dffun.
Variable (F : finType) (TF : F -> ihbFinType) (x : forall i : F, vars (TF i)).
Variable (dis : forall i j, i != j -> [disjoint lb (x i) & lb (x j)]).

Lemma pvars_dffunEt (t : {dffun forall i : F, TF i}) :
  ｜''t; pvars_dffun dis〉 = \tens_i ｜''(t i); x i〉.
Proof. by rewrite pvars_t2tv tenvm_correct. Qed.

Lemma pvars_dffunEv (v : forall i : F, 'Hs (TF i)) :
  ｜tentv_dffun v; pvars_dffun dis〉 = \tens_i ｜v i; x i〉.
Proof. by rewrite pvars_tentv tenvm_correct. Qed.

Lemma pvars_dffunEf (v : forall i : F, 'End[TF i]) :
  ⌈ tentf_dffun v ; pvars_dffun dis ⌉ = \tens_i ⌈ v i ; x i ⌉.
Proof. by rewrite pvars_tentf tenfm_correct. Qed.

Lemma pvars_dffunEt_cst (t : forall i : F, TF i) :
  ｜''([ffun i=> t i] : {dffun forall i : F, TF i}); pvars_dffun dis〉 
    = \tens_i ｜''(t i); x i〉.
Proof. by rewrite pvars_dffunEt; under eq_bigr do rewrite ffunE. Qed.
End pvars_dffun.

Section pvars_ffun.
Variable (F : finType) (T : ihbFinType) (x : F -> vars T).
Variable (dis : forall i j, i != j -> [disjoint lb (x i) & lb (x j)]).

Lemma pvars_ffunEt (t : {ffun F -> T}) :
  ｜''t; pvars_ffun dis〉 = \tens_i ｜''(t i); x i〉.
Proof. exact: pvars_dffunEt. Qed.

Lemma pvars_ffunEv (v : F -> 'Hs T) :
  ｜tentv_ffun v; pvars_ffun dis〉 = \tens_i ｜v i; x i〉.
Proof. exact: pvars_dffunEv. Qed.

Lemma pvars_ffunEf (v : F -> 'End[T]) :
  ⌈ tentf_ffun v ; pvars_ffun dis ⌉ = \tens_i ⌈ v i ; x i ⌉.
Proof. exact: pvars_dffunEf. Qed.

Lemma pvars_ffunEt_cst (t : T) :
  ｜''[ffun i=> t]; pvars_dffun dis〉 = \tens_i ｜''t; x i〉.
Proof. exact: pvars_dffunEt_cst. Qed.
End pvars_ffun.

Definition pvarsEt := (pvars2Ev, pvars_tupleEt, pvars_ffunEt, pvars_dffunEt).
Definition pvarsEv := (pvars2Ev, pvars_tupleEv, pvars_ffunEv, pvars_dffunEv).
Definition pvarsEf := (pvars2Ef, pvars_tupleEf, pvars_ffunEf, pvars_dffunEf).
Definition pvarsEt_cst := (pvars_ffunEt_cst, pvars_dffunEt_cst).

End PackingQExpr.
