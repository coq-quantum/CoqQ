From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.classical Require Import boolp.
From mathcomp.analysis Require Import -(notations)forms.
From mathcomp.analysis Require Import reals.
(* From mathcomp.real_closed Require Import complex. *)
From quantum.external Require Import complex.
Require Import Relation_Definitions.
Require Import Setoid.
(* topology and setoid has notation conflicts *)
(* several lemma in classical_sets and finset have the same name. *)

Require Import mcextra mcaextra notation mxpred autonat.
Require Import hermitian quantum inhabited prodvect tensor qreg qmem.
From quantum.dirac Require Import setdec hstensor dirac.
Import Order.TTheory GRing.Theory Num.Theory Num.Def.
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
(*       (with a bijection vt2i : T -> 'Idx_S which is hide to user).      *) 
(*       the Hilbert space is 'H_(vset x).                                 *)
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
(*   variable x, that is, |v>_x (in dirac scope). For simple use, injection   *)
(*   for two variables is also defined, as tv2v2 / tf2f2                      *)
(* -------------------------------------------------------------------------- *)
(* definition of Hoare triples, global form (lfun), local form (lfun), dirac  *)
(*   form (dirac), state form (dirac, when everything is vector, instead      *)
(*   of writing |v><v|, we can simply write |v> )                             *)
(*   relation : state <-> dirac <-> local -> global                           *)
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
(*   e.g., '[ M , x ] \· '| v ; x > = '| M v ; x >                             *)
(*   we also show that packing variables act as we desired, e.g.,             *)
(*   '| u ⊗t v ; pvars2 x y> = '| u ⊗t v ; (x , y) >                      *)
(*   '| tentv_ffun v ; pvars_ffun x > = \ten_i'| v i ; x i >               *)
(******************************************************************************)

(* automation; use for typeclass_instances *)
(* syntactical decision of well-formedness, disjointness, etc. *)
Class cmd_expose (P : Prop) := CmdExpose : P.
Notation "`{{ P }}" := (cmd_expose P).

Section Syntax.

Inductive cmd_ : Type :=
| abort_
| skip_
| init_      T of qreg T & 'NS('Ht T)
| unitary_   T (x : qreg T) (U : 'FU('Ht T))
| seqc_      of cmd_ & cmd_
| cond_      T (f: finType) (x : qreg T) of 'QM(f;'Ht T) & (f -> cmd_)
| while_     T (x : qreg T) of 'QM(bool;'Ht T) & bool & cmd_.

Fixpoint while_iter_ T (x : qreg T) (M:'QM(bool;'Ht T)) (b : bool) (c: cmd_) n : cmd_:=
  match n with
  | O => abort_
  | S n => cond_ x M (fun b':bool => 
                    if b' == b then seqc_ c (while_iter_ x M b c n)
                    else skip_)
  end.

End Syntax.

Fixpoint fvars (c : cmd_) : {set mlab} :=
  match c with
  | abort_            => set0
  | skip_             => set0
  | init_ T x v       => mset x 
  | unitary_ T x U    => mset x
  | cond_ T F x M fc  => mset x :|: \bigcup_i (fvars (fc i))
  | while_ T x M b c  => mset x :|: (fvars c)
  | seqc_ c1 c2 => (fvars c1) :|: (fvars c2)
  end.

Fixpoint fsem_aux (c : cmd_) : 'SO[msys]_setT := 
  match c with
  | abort_            => 0
  | skip_             => \:1
  | init_ T x v       => liftfso (initialso (tv2v x v))
  | unitary_ T x U    => liftfso (formso (tf2f x x U))
  | cond_ T F x M fc  => ifso (liftf_fun (tm2m x x M)) (fun i : F => fsem_aux (fc i))
  | while_ T x M b c    => whileso (liftf_fun (tm2m x x M)) b (fsem_aux c)
  | seqc_ c1 c2     => (fsem_aux c2) :o (fsem_aux c1)
  end.
HB.lock Definition fsem := fsem_aux.

(* syntactically calculate if quantum register x is disjoint from the program c *)
Fixpoint cmd_var_disj T (x : qreg T) (c : cmd_) :=
    match c with
    | skip_ | abort_ => true
    | init_ _ y _ => disjoint_qreg x y
    | unitary_ _ y _ => disjoint_qreg x y
    | cond_ _ F y _ f => disjoint_qreg x y && [forall i : F, cmd_var_disj x (f i)]
    | while_ _ y _ _ c => disjoint_qreg x y && cmd_var_disj x c
    | seqc_ c1 c2 => cmd_var_disj x c1 && cmd_var_disj x c2 
    end.

Fixpoint cmd_valid (c : cmd_) :=
  match c with
  | skip_ | abort_ => true
  | init_ _ y _ => valid_qreg y
  | unitary_ _ y _ => valid_qreg y
  | cond_ _ F y _ f => valid_qreg y && [forall i : F, cmd_valid (f i)]
  | while_ _ y _ _ c => valid_qreg y && cmd_valid c
  | seqc_ c1 c2 => cmd_valid c1 && cmd_valid c2 
  end.

(* syntactically calculate if two programs are disjoint *)
Fixpoint cmd_disj c1 c2 :=
    match c1 with
    | skip_ | abort_     => true
    | init_ _ x _ => cmd_var_disj x c2
    | unitary_ _ y _  => cmd_var_disj y c2
    | seqc_ c11 c12 => cmd_disj c11 c2 && cmd_disj c12 c2
    | cond_ _ _ x _ f => cmd_var_disj x c2 && [forall i, cmd_disj (f i) c2]
    | while_ _ x _ _ c1 => cmd_var_disj x c2 && cmd_disj c1 c2
    end.

(* x is syntactical disjoint from c -> the quantum systems of x and c are disjoint *)
Lemma cmd_var_disjP T (x : qreg T) (c : cmd_) :
    cmd_var_disj x c -> [disjoint mset x & fvars c].
Proof.
elim: c=>/=.
1,2: by rewrite disjointX0.
1,2: by move=>???; rewrite -disj_setE.
by move=>? IH1 ? IH2 /andP[] /IH1 + /IH2; rewrite disjointXU=>->->.
- move=>? ? y ? fu IH /andP[] + /forallP Pi.
  rewrite disjointXU -disj_setE=>-> /=.
  by apply/bigcup_disjoint=>i _; apply/IH/Pi.
- move=>? y ? ? ? IH /andP[] + /IH.
  by rewrite disjointXU -disj_setE=>->->.
Qed.

(* disjoint programs acts on disjoint systems *)
Lemma cmd_disjP c1 c2 :
    cmd_disj c1 c2 -> [disjoint fvars c1 & fvars c2].
Proof.
elim: c1.
1,2: by rewrite /= disjoint0X.
1,2: by move=>???/=/cmd_var_disjP.
by move=>? IH1 ? IH2/=/andP[]/IH1+/IH2; rewrite disjointUX=>->->.
move=>????? IH/=/andP[]/cmd_var_disjP+/forallP Pi.
rewrite disjointUX=>->/=; rewrite disjoint_sym bigcup_disjoint// =>i _;
by rewrite disjoint_sym IH.
by move=>?????/= IH/andP[]/cmd_var_disjP+/IH; rewrite disjointUX=>->->.
Qed.

Lemma cmd_disjC c1 c2 : cmd_disj c1 c2 = cmd_disj c2 c1.
Proof.
elim: c1 c2=>/=.
1,2: elim=>//=[?<-?<-//|????? IH]; by symmetry; apply/forallP.
1,2: move=>???; elim=>//=[???|???|?->?->//|????? IH|????? <-];
  rewrite QRegAuto.disjoint_qregC//; f_equal;
  by under eq_forallb do rewrite IH.
- move=>? IH1? IH2 c2; rewrite IH1 IH2; elim: c2=>//=.
  - by move=>?<-?<-; rewrite !andbA; f_equal; rewrite -!andbA; f_equal; rewrite andbC.
  - by move=>????? IH; rewrite andbACA forallb_and; under eq_forallb do rewrite IH.
  - by move=>????? IH; rewrite andbACA IH.
- move=>????? IH; elim=>//=.
  1,2: by apply/forallP=>?; rewrite IH.
  1,2: by move=>???; rewrite QRegAuto.disjoint_qregC; under eq_forallb do rewrite IH.
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
  - move=>?????<-; rewrite andbACA QRegAuto.disjoint_qregC forallb_and; f_equal.
    by under eq_forallb do rewrite IH/= -IH.
- move=>????? IH; elim=>//=.
  1,2: by move=>???; rewrite QRegAuto.disjoint_qregC IH.
  - by move=>?<-?<-; rewrite andbACA; f_equal; rewrite !IH/=.
  - move=>????? IH1; rewrite IH/= andbACA QRegAuto.disjoint_qregC; f_equal.
    by rewrite forallb_and; under eq_forallb do rewrite -IH IH1.
  - by move=>?????<-; rewrite !IH/= andbACA QRegAuto.disjoint_qregC.
Qed.

(* pack the validity, canonical structure *)
Structure wf_cmd := WF_CMD {
  cmd_base : cmd_;
  cmd_is_valid : cmd_valid cmd_base;
}.
#[reversible] Coercion cmd_base : wf_cmd >-> cmd_.
Canonical cmd_wf (c : cmd_) {H : cmd_expose (cmd_valid c)} := WF_CMD H.
Definition clone_wf_cmd e :=
  fun (opL : wf_cmd) & (@phant_id cmd_ cmd_ opL e) =>
  fun ewf (opL' := @WF_CMD e ewf)
    & phant_id opL' opL => opL'.

Notation "'Cmd_'" := (wf_cmd) : type_scope.
Notation "[ 'wf_cmd' 'of' c ]" := (@clone_wf_cmd c _ id _ id)
  (at level 0, format "[ 'wf_cmd'  'of'  c  ]") : form_scope.

Section Semantics.

Lemma fsem_abortE : fsem abort_ = 0.
Proof. by rewrite [fsem]unlock. Qed.

Lemma fsem_skipE : fsem skip_ = \:1.
Proof. by rewrite [fsem]unlock. Qed.

Lemma fsem_initE T x v : fsem (@init_ T x v) = liftfso (initialso (tv2v x v)).
Proof. by rewrite [fsem]unlock. Qed.

Lemma fsem_unitaryE T x U : fsem (@unitary_ T x U) = liftfso (formso (tf2f x x U)).
Proof. by rewrite [fsem]unlock. Qed.

Lemma fsem_ifE T F x M fc : fsem (@cond_ T F x M fc) = 
  ifso (liftf_fun (tm2m x x M)) (fun i : F => fsem (fc i)).
Proof. by rewrite [fsem]unlock. Qed.

Lemma fsem_whileE T x M b c : fsem (@while_ T x M b c) = 
  whileso (liftf_fun (tm2m x x M)) b (fsem c).
Proof. by rewrite [fsem]unlock. Qed.

Lemma fsem_seqE c1 c2 :
  fsem (seqc_ c1 c2) = (fsem c2) :o (fsem c1).
Proof. by rewrite [fsem]unlock. Qed.

Definition fsemE := (fsem_abortE, fsem_skipE, fsem_initE, 
  fsem_unitaryE, fsem_ifE, fsem_seqE, fsem_whileE).

Lemma fsem_while_iter_ T x M b (c: cmd_) n :
  fsem (@while_iter_ T x M b c n) = 
    whileso_iter (liftf_fun (tm2m x x M)) b (fsem c) n.
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
Lemma fsem_qo (c : cmd_) : fsem c \is cptn.
Proof.
elim: c=>[||T x v|T x U|c1 IH c2 IH1|T F x M br IH|T x M b D IH]/=; rewrite fsemE.
6: have->: (fun i : F => fsem (br i)) = (fun i : F => QOperation_Build (IH i)) by [].
5,7: rewrite (QOperation_BuildE IH) 1?(QOperation_BuildE IH1).
all: apply/is_cptn.
Qed.
HB.instance Definition _ (c : cmd_) := isQOperation.Build _ _ _ (fsem_qo c).

(* check program contains while; if not, quantum channel *)
Fixpoint no_while (c : cmd_) :=
  match c with
  | abort_            => false
  | skip_             => true
  | init_ T x v       => true
  | unitary_ T x U    => true
  | cond_ T F x M fc  => \big[andb/true]_(i : F) (no_while (fc i))
  | while_ T x M b c  => false
  | seqc_ c1 c2       => (no_while c1) && (no_while c2)
  end.

(* check program is pure, i.e., without initialization and if while; NS -> NS *)
Fixpoint pure_cmd (c : cmd_) :=
  match c with
  | abort_            => false
  | skip_             => true
  | init_ T x v       => false
  | unitary_ T x U    => true
  | cond_ T x F M fc  => false
  | while_ T x M b c  => false
  | seqc_ c1 c2       => (pure_cmd c1) && (pure_cmd c2)
  end.

Lemma no_while_qc c : no_while c -> cmd_valid c -> fsem c \is cptp.
Proof.
elim: c=>[|_ _|T x v _ /= Px|T x U _ /= Px|c H1 c1 H2|T F x M br IH|]//=; rewrite fsemE.
4: move=>/andP[P1 P2]/andP[/(H1 P1) Q1 /(H2 P2) Q2]; 
  rewrite (QChannel_BuildE Q1) (QChannel_BuildE Q2).
5: rewrite big_andE=>/forallP/=P /andP[Px] /forallP Pi;
  have ->: (fun i => fsem (br i)) = (fun i => QChannel_Build (IH i (P i) (Pi i))) by [].
all: apply/is_cptp.
Qed.

(* local denotational semantics *)
Lemma fsem_local c : exists E : 'QO[msys]_(fvars c), fsem c = liftfso E.
Proof.
elim: c=>[||T x v|T x U|c1 [E1 P1] c2 [E2 P2]|T F x M br IH|T x M b c [E P]] =>/=.
- by exists [QO of 0]; rewrite/= fsemE linear0.
- by exists \:1; rewrite/= fsemE liftfso1.
- by exists (initialso (tv2v x v)); rewrite fsemE.
- by exists (formso (tf2f x x U)); rewrite fsemE.
- exists (liftso (subsetUr _ _) E2 :o (liftso (subsetUl _ _) E1)).
  by rewrite fsemE liftfso_comp !liftfso2 P1 P2.
- pose f i := projT1 (cid (IH i)).
  have P i : fsem (br i) = liftfso (f i).
    by move: (projT2 (cid (IH i))).
  move: (subsetUl (mset x) (\bigcup_i fvars (br i)))=>sub.
  have subi i : fvars (br i) :<=: mset x :|: \bigcup_i fvars (br i).
    by apply/subsetU/orP; right; apply/bigcup_sup.
  exists (ifso (lift_fun sub (tm2m x x M)) (fun i=>liftso (subi i) (f i))) =>/=.
  by rewrite fsemE liftfso_ifso liftf_fun2; f_equal; apply/funext=>i; rewrite liftfso2.
- exists (whileso (lift_fun (subsetUl (mset x) (fvars c)) (tm2m x x M)) 
    b (liftso (subsetUr _ _) E)).
  by rewrite fsemE liftfso_whileso/= liftf_fun2 liftfso2 P.
Qed.

Lemma fsem_lift (S : {set mlab}) c : fvars c :<=: S -> 
  exists E : 'QO[msys]_S, fsem c = liftfso E.
Proof.
move=>P1; move: (fsem_local c)=>[E PE].
exists (liftso P1 E); by rewrite/= liftfso2.
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

Notation "'SKIP'" := (skip_) : lfun_scope.
Notation "'ABORT'" := (abort_) : lfun_scope.
Notation " c1 ';;' c2 " := (seqc_ c1 c2) 
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
  (\big[seqc_ /skip_ ]_(i <- r | P%B) F%VF) : lfun_scope.
Notation "[ 'for' i <- r 'do' F ]" :=
  (\big[seqc_ /skip_ ]_(i <- r) F%VF) : lfun_scope.
Notation "[ 'for' m <= i < n | P 'do' F ]" :=
  (\big[seqc_ /skip_ ]_(m <= i < n | P%B) F%VF) : lfun_scope.
Notation "[ 'for' m <= i < n 'do' F ]" :=
  (\big[seqc_ /skip_ ]_(m <= i < n) F%VF) : lfun_scope.
Notation "[ 'for' i | P 'do' F ]" :=
  (\big[seqc_ /skip_ ]_(i | P%B) F%VF) : lfun_scope.
Notation "[ 'for' i 'do' F ]" :=
  (\big[seqc_ /skip_ ]_i F%VF) : lfun_scope.
Notation "[ 'for' i : t | P 'do' F ]" :=
  (\big[seqc_ /skip_ ]_(i : t | P%B) F%VF) (only parsing) : lfun_scope.
Notation "[ 'for' i : t 'do' F ]" :=
  (\big[seqc_ /skip_ ]_(i : t) F%VF) (only parsing) : lfun_scope.
Notation "[ 'for' i < n | P 'do' F ]" :=
  (\big[seqc_ /skip_ ]_(i < n | P%B) F%VF) : lfun_scope.
Notation "[ 'for' i < n 'do' F ]" :=
  (\big[seqc_ /skip_ ]_(i < n) F%VF) : lfun_scope.
Notation "[ 'for' i 'in' A | P 'do' F ]" :=
  (\big[seqc_ /skip_ ]_(i in A | P%B) F%VF) : lfun_scope.
Notation "[ 'for' i 'in' A 'do' F ]" :=
  (\big[seqc_ /skip_ ]_(i in A) F%VF) : lfun_scope.

(* Notation "x <<- e" := (@init_ _ _ x e) 
  (at level 65, e at level 70, no associativity, format "x  <<-  e") : lfun_scope. *)
(* Notation "'If' M [ F ; S ] 'then' f" := (@cond_ _ _ _ F S M f) 
  (at level 65, right associativity, format
"'If'  M [ F ; S ]  'then'  f") : lfun_scope.
Notation "'While' M [ S ] 'Do' c" := (@while_ _ _ _ S M c) 
  (at level 65, right associativity, format
"'While'  M [ S ]  'Do'  c") : lfun_scope. *)

Lemma no_while_for F (r : seq F) (P : pred F) (c : F -> cmd_) :
  (forall i, P i -> no_while (c i)) ->
    no_while [for i <- r | P i do c i].
Proof. by move=>Pi; elim/big_rec: _=>[//|i x IH]; rewrite /= Pi. Qed.

Lemma cmd_valid_for F (r : seq F) (P : pred F) (c : F -> cmd_) :
  (forall i, P i -> cmd_valid (c i)) ->
    cmd_valid [for i <- r | P i do c i].
Proof. by move=>Pi; elim/big_rec: _=>[//|i x IH]; rewrite /= Pi. Qed.

Lemma fvars_for (T : Type) (r : seq T) (P : pred T) (fp : T -> cmd_) :
    fvars [for i <- r | P i do (fp i)] = \bigcup_(i<-r|P i) (fvars (fp i)).
Proof.
elim: r=>[|x r IH]; first by rewrite !big_nil/=.
rewrite !big_cons; case: (P x)=>/=; by rewrite IH.
Qed. 

Lemma cmd_var_disj_for (T : eqType) (r : seq T) (P : pred T) (fp : T -> cmd_) 
  I (x : qreg I) :
    (forall i, P i -> cmd_var_disj x (fp i)) ->
      cmd_var_disj x [for i <- r | P i do (fp i)].
Proof. by move=>H; elim/big_rec: _=>//= ?? /H->->. Qed.

Lemma cmd_disj_for (T : eqType) (r : seq T) (P : pred T) (fp : T -> cmd_) c :
    (forall i, P i -> cmd_disj (fp i) c) ->
      cmd_disj [for i <- r | P i do (fp i)] c.
Proof. by move=>H; elim/big_rec: _=>//= ?? /H->->. Qed.

Lemma cmd_disj_forC (T : eqType) (r : seq T) (P : pred T) (fp : T -> cmd_) c :
    (forall i, P i -> cmd_disj c (fp i)) ->
      cmd_disj c [for i <- r | P i do (fp i)].
Proof. by move=>H; rewrite cmd_disjC cmd_disj_for// =>?/H; rewrite cmd_disjC. Qed.

HB.lock
Definition eqcmd (c1 c2 : cmd_) := fsem c1 = fsem c2.
Infix "=s" := eqcmd (at level 70) : lfun_scope.

Lemma eqcmd_trans : 
  forall (a b c: cmd_), a =s b -> b =s c -> a =s c.
Proof. by rewrite eqcmd.unlock; move=>a b c -> ->. Qed.

Lemma eqcmd_refl : forall (a: cmd_), a =s a.
Proof. by rewrite eqcmd.unlock. Qed.

Lemma eqcmd_sym : forall (a b : cmd_), a =s b -> b =s a.
Proof. by rewrite eqcmd.unlock; move=>a b ->. Qed.

Global Hint Resolve eqcmd_refl : core.
Global Hint Resolve index_enum_uniq : core.

Add Parametric Relation : cmd_ eqcmd
  reflexivity proved by eqcmd_refl
  symmetry proved by eqcmd_sym
  transitivity proved by eqcmd_trans
  as eqcmd_rel.

Notation "[ 'it' x ':=' v ]" := (init_ x v%VF) 
  (at level 0, x custom reg, no associativity, format "[ 'it'  x  ':='  v ]") : lfun_scope.
Notation "[ 'ut' x ':=' U ]" := (unitary_ x U%VF)
  (at level 0, x custom reg, no associativity, format "[ 'ut'  x  ':='  U ]") : lfun_scope.
Notation "[ 'if' M [ x ] '=' t 'then' F ]" := (cond_ x M (fun t => F)) 
  (at level 0, x custom reg, right associativity, format
    "[ 'if'  M [ x ]  '='  t  'then'  F ]") : lfun_scope.
Notation "[ 'while' M [ x ] '=' b 'do' c ]" := (while_ x M b c) 
  (at level 0, x custom reg, right associativity, format
    "[ 'while'  M [ x ]  '='  b  'do'  c ]") : lfun_scope.

Lemma eq_init T (x1 x2 : qreg T) (v1 v2 : 'NS) :
  x1 =r x2 -> v1 = v2 :> 'Ht _ -> [it x1 := v1] =s [it x2 := v2].
Proof.
move=>Px Pu; rewrite eqcmd.unlock !fsemE Pu -(tv2v_eqr _ Px)/=.
move: (mset_eqr default_qmemory Px) => P.
by case: _ / P; rewrite casths_id.
Qed.

Lemma eq_initl T (x1 x2 : qreg T) (v : 'NS) :
  x1 =r x2 -> [it x1 := v] =s [it x2 := v].
Proof. by move=>P; apply/eq_init. Qed.

Lemma eq_initr T (x : qreg T) (v1 v2 : 'NS) :
  v1 = v2 :> 'Ht _ -> [it x := v1] =s [it x := v2].
Proof. by move=>P; apply/eq_init. Qed.

Lemma eq_unit T (x1 x2 : qreg T) (U1 U2 : 'FU) :
  x1 =r x2 -> U1 = U2 :> 'End(_) -> [ut x1 := U1] =s [ut x2 := U2].
Proof.
move=>Px Pu; rewrite eqcmd.unlock !fsemE /unitaryso/= -(tf2f_eqr _ Px Px)/=.
by rewrite !liftfso_formso/= liftf_lf_cast Pu.
Qed.

Lemma eq_unitl T (x1 x2 : qreg T) (U : 'FU) :
  x1 =r x2 -> [ut x1 := U] =s [ut x2 := U].
Proof. by move=>P; apply/eq_unit. Qed.

Lemma eq_unitr T (x : qreg T) (U1 U2 : 'FU) :
  U1 = U2 :> 'End(_) -> [ut x := U1] =s [ut x := U2].
Proof. by move=>P; apply/eq_unit. Qed.

Lemma eq_cond T (F: finType) (x1 x2 : qreg T) (M1 M2 : 'QM(F;'Ht T)) (f1 f2 : F -> cmd_) :
  x1 =r x2 -> M1 =1 M2 -> (forall i, f1 i =s f2 i) ->
  [if M1[x1] = t then f1 t] =s [if M2[x2] = t then f2 t].
Proof.
rewrite eqcmd.unlock=>Px PM Pf; rewrite !fsemE; under eq_fun do rewrite Pf.
do 3 f_equal.
by apply/funext=>i; rewrite !liftf_funE !tm2mE PM -(tf2f_eqr _ Px Px) liftf_lf_cast.
Qed.

Lemma eq_condl T (F: finType) (x1 x2 : qreg T) (M : 'QM(F;'Ht T)) (f : F -> cmd_) :
  x1 =r x2 ->
  [if M[x1] = t then f t] =s [if M[x2] = t then f t].
Proof. by move=>P; apply/eq_cond. Qed.

Lemma eq_condm T (F: finType) (x : qreg T) (M1 M2 : 'QM(F;'Ht T)) (f : F -> cmd_) :
  M1 =1 M2 ->
  [if M1[x] = t then f t] =s [if M2[x] = t then f t].
Proof. by move=>P; apply/eq_cond. Qed.

Lemma eq_condr T (F: finType) (x : qreg T) (M : 'QM(F;'Ht T)) (f1 f2 : F -> cmd_) :
  (forall i, f1 i =s f2 i) ->
  [if M[x] = t then f1 t] =s [if M[x] = t then f2 t].
Proof. by move=>P; apply/eq_cond. Qed.

Lemma eq_while T (x1 x2 : qreg T) (M1 M2 : 'QM(bool;'Ht T)) b (c1 c2 : cmd_) :
  x1 =r x2 -> M1 =1 M2 -> c1 =s c2 ->
  [while M1[x1] = b do c1] =s [while M2[x2] = b do c2].
Proof.
rewrite eqcmd.unlock=>Px PM Pf; rewrite !fsemE Pf; do 3 f_equal.
by apply/funext=>i; rewrite !liftf_funE !tm2mE PM -(tf2f_eqr _ Px Px) liftf_lf_cast.
Qed.

Lemma eq_whilel T (x1 x2 : qreg T) (M : 'QM(bool;'Ht T)) b c :
  x1 =r x2 ->
  [while M[x1] = b do c] =s [while M[x2] = b do c].
Proof. by move=>P; apply/eq_while. Qed.

Lemma eq_whilem T (x : qreg T) (M1 M2 : 'QM(bool;'Ht T)) b c :
  M1 =1 M2 ->
  [while M1[x] = b do c] =s [while M2[x] = b do c].
Proof. by move=>P; apply/eq_while. Qed.

Lemma eq_whiler T (x : qreg T) (M : 'QM(bool;'Ht T)) b (c1 c2 : cmd_) :
  c1 =s c2 ->
  [while M[x] = b do c1] =s [while M[x] = b do c2].
Proof. by move=>P; apply/eq_while. Qed.

Add Parametric Morphism T : (@init_ T) 
  with signature (@eq_qreg T) ==> (@eq _) ==> (eqcmd) as eq_init_mor.
Proof. by move=>????; apply/eq_init. Qed.

Add Parametric Morphism T : (@unitary_ T) 
  with signature (@eq_qreg T) ==> (@eq _) ==> (eqcmd) as eq_unit_mor.
Proof. by move=>????; apply/eq_unit. Qed.

Add Parametric Morphism T (F : finType): (@cond_ T F) 
  with signature (@eq_qreg T) ==> (@eq _) ==> (@eq _) ==> (eqcmd) as eq_cond_mor.
Proof. by move=>?????; apply/eq_cond. Qed.

Add Parametric Morphism T : (@while_ T) 
  with signature (@eq_qreg T) ==> (@eq _) ==> (@eq bool) ==> (eqcmd) ==> (eqcmd) as eq_while_mor.
Proof. by move=>????????; apply/eq_while. Qed.

Add Parametric Morphism : (seqc_)
  with signature (eqcmd) ==> (eqcmd) ==> (eqcmd) as eq_seqc.
Proof. by rewrite eqcmd.unlock=>?? H1 ?? H2; rewrite !fsemE H1 H2. Qed.

Lemma eq_for I (r : seq I) (P1 P2 : pred I) (f1 f2 : I -> cmd_) :
  P1 =1 P2 -> (forall i, P1 i -> f1 i =s f2 i) ->
    [for i <- r | P1 i do f1 i ] =s [for i <- r | P2 i do f2 i ].
Proof.
move=>H Hi; elim: r; first by rewrite !big_nil.
move=>a l IH; rewrite !big_cons -H; case E: (P1 a)=>//.
by rewrite Hi// IH.
Qed.

Lemma eq_forl I (r : seq I) (P1 P2 : pred I) (f : I -> cmd_) :
  P1 =1 P2 ->
    [for i <- r | P1 i do f i ] =s [for i <- r | P2 i do f i ].
Proof. by move/eq_for; apply. Qed.

Lemma eq_forr I (r : seq I) (P : pred I) (f1 f2 : I -> cmd_) :
  (forall i, P i -> f1 i =s f2 i) ->
    [for i <- r | P i do f1 i ] =s [for i <- r | P i do f2 i ].
Proof. by apply: eq_for. Qed.

Lemma eq_for_ord_recr n (F : 'I_n.+1 -> cmd_) :
  [for i do F i] =s ([for i do F (widen_ord (leqnSn n) i)] ;; F ord_max).
Proof. by rewrite eqcmd.unlock fsemE !fsem_big big_ord_recr/= comp_soElr. Qed.

Lemma fsem_seqA (c1 c2 c3 : cmd_) : (c1 ;; (c2 ;; c3)) =s (c1 ;; c2 ;; c3).
Proof. by rewrite eqcmd.unlock fsem_seqcA. Qed.

Lemma fsem_seqC (c1 c2 : cmd_) {H : `{{ cmd_disj c1 c2 }}} : 
  (c1 ;; c2) =s (c2 ;; c1).
Proof. by rewrite eqcmd.unlock fsem_seqcC//; apply/cmd_disjP. Qed.  

Lemma fsem_seqC_mset (c1 c2 : cmd_) {H : [disjoint fvars c1 & fvars c2]} : 
  (c1 ;; c2) =s (c2 ;; c1).
Proof. by rewrite eqcmd.unlock fsem_seqcC. Qed.

(* predicates are observables over full space : 'FO_setT *)
(* there are two boolean variables, pt : false - partial , true - toal *)
(* st : false - may not saturated , true saturated (the weakest (literal) precondition)*)
(* pt and st are introduced to avoid messy amount of rules *)
HB.lock
Definition global_hoare (pt st : bool) (P: 'FO_setT) (Q: 'FO_setT) (c: cmd_) :=
  (forall (x : 'FD_setT),
  if pt then
    if st then \Tr (P \o x) = \Tr (Q \o ((fsem c) x))
          else \Tr (P \o x) <= \Tr (Q \o ((fsem c) x))
  else
    if st then \Tr (Q^⟂ \o ((fsem c) x)) = \Tr (P^⟂ \o x)
          else \Tr (Q^⟂ \o ((fsem c) x)) <= \Tr (P^⟂ \o x)  ).

HB.lock
Definition local_hoare (pt st : bool) S T (P: 'F_S) (Q: 'F_T) (c: cmd_) :=
  (forall (x : 'FD_setT),
  if pt then
    if st then \Tr (liftf_lf P \o x) = \Tr (liftf_lf Q \o ((fsem c) x))
          else \Tr (liftf_lf P \o x) <= \Tr (liftf_lf Q \o ((fsem c) x))
  else
    if st then \Tr (liftf_lf Q^⟂ \o ((fsem c) x)) = \Tr (liftf_lf P^⟂ \o x)
          else \Tr (liftf_lf Q^⟂ \o ((fsem c) x)) <= \Tr (liftf_lf P^⟂ \o x)  ).

HB.lock
Definition dirac_hoare (pt st : bool) (P Q : 'D) (c: cmd_) :=
  exists S T, (sqrdirac_axiom S P /\ sqrdirac_axiom T Q /\ local_hoare pt st (P S S) (Q T T) c).

HB.lock
Definition state_hoare (pt st : bool) (P Q : 'D) (c: cmd_) :=
  dirac_hoare pt st (P \o P^A) (Q \o Q^A) c.

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

Notation "'⊨p' { P } c { Q }" := (dirac_hoare false false P Q c)
  (at level 10, P,c,Q at next level, format "'⊨p' {  P  }  c  {  Q  }" ).
Notation "'⊫p' { P } c { Q }" := (dirac_hoare false true P Q c)
  (at level 10, P,c,Q at next level, format "'⊫p' {  P  }  c  {  Q  }" ).
Notation "'⊨t' { P } c { Q }" := (dirac_hoare true false P Q c)
  (at level 10, P,c,Q at next level, format "'⊨t' {  P  }  c  {  Q  }" ).
Notation "'⊫t' { P } c { Q }" := (dirac_hoare true true P Q c)
  (at level 10, P,c,Q at next level, format "'⊫t' {  P  }  c  {  Q  }" ).
Notation "'⊨' [ pt ] { P } c { Q }" := (dirac_hoare pt false P Q c)
  (at level 10, pt,P,c,Q at next level, format "'⊨' [ pt ] {  P  }  c  {  Q  }" ).
Notation "'⊫' [ pt ] { P } c { Q }" := (dirac_hoare pt true P Q c)
  (at level 10, pt,P,c,Q at next level, format "'⊫' [ pt ] {  P  }  c  {  Q  }" ).
Notation "'⊨p' [ st ] { P } c { Q }" := (dirac_hoare false st P Q c)
  (at level 10, st,P,c,Q at next level, format "'⊨p' [ st ] {  P  }  c  {  Q  }" ).
Notation "'⊨t' [ st ] { P } c { Q }" := (dirac_hoare true st P Q c)
  (at level 10, st,P,c,Q at next level, format "'⊨t' [ st ] {  P  }  c  {  Q  }" ).
Notation "'⊨' [ pt , st ] { P } c { Q }" := (dirac_hoare pt st P Q c)
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

Add Parametric Morphism pt st P Q : 
  (@global_hoare pt st P Q)
  with signature (eqcmd) ==> iff as eqcmd_hoare_mor.
Proof.
move=>x y; rewrite eqcmd.unlock global_hoare.unlock=>H1; split=>P1 z.
rewrite -H1; apply P1. rewrite H1; apply P1.
Qed.

Add Parametric Morphism pt st S T P Q : 
  (@local_hoare pt st S T P Q)
  with signature (eqcmd) ==> iff as eqcmd_local_hoare_mor.
Proof.
move=>x y; rewrite eqcmd.unlock local_hoare.unlock=>H1; split=>P1 z.
rewrite -H1; apply P1. rewrite H1; apply P1.
Qed.

Add Parametric Morphism pt st (P Q : 'D) : 
  (@dirac_hoare pt st P Q)
  with signature (eqcmd) ==> iff as eqcmd_dirac_hoare_mor.
Proof.
by move=>x y Pxy; rewrite dirac_hoare.unlock; split; move=>[S[T[Ps[Pt Px]]]]; 
exists S; exists T; do 2 split=>//; move: Px; rewrite Pxy.
Qed.

Add Parametric Morphism pt st (P Q : 'D) : 
  (@state_hoare pt st P Q)
  with signature (eqcmd) ==> iff as eqcmd_dirac_hoare_form_mor.
Proof. by move=>x y Pxy; rewrite state_hoare.unlock Pxy. Qed.

Lemma eq_state_hoare pt st P1 P2 Q1 Q2 c1 c2 :
  P1 = P2 -> c1 =s c2 -> Q1 = Q2 ->
  ⊨s [pt,st] {P1} c1 {Q1} -> ⊨s [pt,st] {P2} c2 {Q2}.
Proof. by move=>->->->. Qed.

Lemma eq_dirac_hoare pt st P1 P2 Q1 Q2 c1 c2 :
  P1 = P2 -> c1 =s c2 -> Q1 = Q2 ->
  ⊨ [pt,st] {P1} c1 {Q1} -> ⊨ [pt,st] {P2} c2 {Q2}.
Proof. by move=>->->->. Qed.

Section TrivalHoare.
Local Open Scope dirac_scope.

Lemma saturated_strong_G pt st P Q c :
  ⊫g [ pt ] { P } c { Q } -> ⊨g [ pt , st ] { P } c { Q }.
Proof. by case: st=>//; case: pt; rewrite global_hoare.unlock=>P1 x; rewrite P1. Qed.
Lemma saturated_strong_L pt st S T (P: 'F_S) (Q: 'F_T) c :
  ⊫l [ pt ] { P } c { Q } -> ⊨l [ pt , st ] { P } c { Q }.
Proof. by case: st=>//; case: pt; rewrite local_hoare.unlock=>P1 x; rewrite P1. Qed.
Lemma saturated_strong pt st (P: 'D) (Q: 'D) c :
  ⊫ [ pt ] { P } c { Q } -> ⊨ [ pt , st ] { P } c { Q }.
Proof.
rewrite dirac_hoare.unlock=>[[S[T[Ps[Pt Pl]]]]]; exists S; exists T; 
by do 2 split=>//; apply/saturated_strong_L.
Qed.
Lemma saturated_strongS pt st (P: 'D) (Q: 'D) c :
  ⊫s [ pt ] { P } c { Q } -> ⊨s [ pt , st ] { P } c { Q }.
Proof. rewrite state_hoare.unlock; exact: saturated_strong. Qed.

Lemma saturated_weak_G pt st P Q c :
  ⊨g [ pt , st ] { P } c { Q } -> ⊨g [ pt ] { P } c { Q }.
Proof. case: st=>//; exact: saturated_strong_G. Qed.
Lemma saturated_weak_L pt st S T (P: 'F_S) (Q: 'F_T) c :
  ⊨l [ pt , st ] { P } c { Q } -> ⊨l [ pt ] { P } c { Q }.
Proof. case: st=>//; exact: saturated_strong_L. Qed.
Lemma saturated_weak pt st (P: 'D) (Q: 'D) c :
  ⊨ [ pt , st ] { P } c { Q } -> ⊨ [ pt ] { P } c { Q }.
Proof. case: st=>//; exact: saturated_strong. Qed.
Lemma saturated_weakS pt st (P: 'D) (Q: 'D) c :
  ⊨s [ pt , st ] { P } c { Q } -> ⊨s [ pt ] { P } c { Q }.
Proof. case: st=>//; exact: saturated_strongS. Qed.

Lemma partial_alter_G (st : bool) (P: 'FO_setT) (Q: 'FO_setT) c :
  ⊨g [ false , st ] { P } c { Q } <-> 
  (forall (x : 'FD_setT), 
  if st then \Tr (P \o x) = \Tr (Q \o ((fsem c) x)) + \Tr x - \Tr ((fsem c) x)
        else \Tr (P \o x) <= \Tr (Q \o ((fsem c) x)) + \Tr x - \Tr ((fsem c) x) ).
Proof.
rewrite global_hoare.unlock; case: st; split=>H1 x; 
move: (H1 x); rewrite -[in \Tr (fsem c x)](comp_lfun1l (fsem c x))
  addrAC -linearB/= -linearBl/= -opprB cplmtE linearNl/= linearN/=.
move=>->. 2: move=>/eqP; rewrite -subr_eq -eqr_oppLR=>/eqP<-.
1,2: by rewrite -cplmtE linearBl/= comp_lfun1l !linearB/= opprB// addrNK.
all: by rewrite -[\Tr x]opprK lerBrDr lerNr opprB 
  -[in \Tr x](comp_lfun1l x) -linearB/= -linearBl/= cplmtE.
Qed.

Lemma partial_alter_L (st : bool) S T (P: 'F_S) (Q: 'F_T) c :
  ⊨l [ false , st ] { P } c { Q } <-> 
  (forall (x : 'FD_setT), 
  if st then \Tr (liftf_lf P \o x) = \Tr (liftf_lf Q \o ((fsem c) x)) + \Tr x - \Tr ((fsem c) x)
        else \Tr (liftf_lf P \o x) <= \Tr (liftf_lf Q \o ((fsem c) x)) + \Tr x - \Tr ((fsem c) x) ).
Proof.
rewrite local_hoare.unlock; case: st; split=>H1 x; 
move: (H1 x); rewrite -[in \Tr (fsem c x)](comp_lfun1l (fsem c x))
  addrAC -linearB/= -linearBl/= -opprB cplmtE linearNl/= linearN/= !liftf_lf_cplmt.
move=>->. 2: move=>/eqP; rewrite -subr_eq -eqr_oppLR=>/eqP<-.
1,2: by rewrite -cplmtE linearBl/= comp_lfun1l !linearB/= opprB// addrNK.
all: by rewrite -[\Tr x]opprK lerBrDr lerNr opprB 
  -[in \Tr x](comp_lfun1l x) -linearB/= -linearBl/= cplmtE.
Qed.

Lemma relation_GPT st c P Q : 
  fsem c \is cptp -> ⊨g [false,st] { P } c { Q } <-> ⊨g [true,st] { P } c { Q }.
Proof.
move=>IH; rewrite partial_alter_G global_hoare.unlock; 
by split=>H1 x; move: (H1 x); rewrite (QChannel_BuildE IH) qc_trlfE addrK.
Qed.
Global Arguments relation_GPT [st c P Q].

Lemma no_while_GPT st c P Q : no_while c -> cmd_valid c ->
  ⊨g [false,st] { P } c { Q } <-> ⊨g [true,st] { P } c { Q }.
Proof. by move=> P1 /(no_while_qc P1); exact: relation_GPT. Qed.
Global Arguments no_while_GPT [st c P Q].

Lemma relation_LPT st c S T (P: 'F_S) (Q: 'F_T) : 
  fsem c \is cptp -> ⊨l [false,st] { P } c { Q } <-> ⊨l [true,st] { P } c { Q }.
Proof.
move=>IH; rewrite partial_alter_L local_hoare.unlock; 
by split=>H1 x; move: (H1 x); rewrite (QChannel_BuildE IH) qc_trlfE addrK.
Qed.
Global Arguments relation_LPT [st c S T P Q].

Lemma no_while_LPT st c S T (P: 'F_S) (Q: 'F_T) : no_while c -> cmd_valid c ->
  ⊨l [false,st] { P } c { Q } <-> ⊨l [true,st] { P } c { Q }.
Proof. by move=>P1 /(no_while_qc P1); exact: relation_LPT. Qed.
Global Arguments no_while_LPT [st c S T P Q].

Lemma relation_PT st c (P Q : 'D) : 
  fsem c \is cptp -> ⊨ [false,st] { P } c { Q } <-> ⊨ [true,st] { P } c { Q }.
Proof.
split; rewrite dirac_hoare.unlock=>[[S] [T] [PS] [PT] IH]; 
exists S; exists T; do 2 split=>//.
by rewrite -relation_LPT. by rewrite relation_LPT.
Qed.
Global Arguments relation_PT [st c P Q].

Lemma no_while_PT st c (P Q : 'D) : no_while c -> cmd_valid c ->
  ⊨ [false,st] { P } c { Q } <-> ⊨ [true,st] { P } c { Q }.
Proof. by move=>P1 /(no_while_qc P1); exact: relation_PT. Qed.
Global Arguments no_while_PT [st c P Q].

Lemma relation_SPT st c (P Q : 'D) : 
  fsem c \is cptp -> ⊨s [false,st] { P } c { Q } <-> ⊨s [true,st] { P } c { Q }.
Proof. rewrite state_hoare.unlock; exact: relation_PT. Qed.
Global Arguments relation_SPT [st c P Q].

Lemma no_while_SPT st c (P Q : 'D) : no_while c -> cmd_valid c ->
  ⊨s [false,st] { P } c { Q } <-> ⊨s [true,st] { P } c { Q }.
Proof. rewrite state_hoare.unlock; exact: no_while_PT. Qed.
Global Arguments no_while_SPT [st c P Q].

End TrivalHoare.


(*****************************************************************************)
(*                                 Automation                                *)
(*****************************************************************************)
(* solving cmd_expose *)
Module Export QWhileAuto.

HB.lock Definition cmd_var_disj_lock := cmd_var_disj.
Lemma cmd_var_disj_lockE : cmd_var_disj = cmd_var_disj_lock.
Proof. by rewrite cmd_var_disj_lock.unlock. Qed.
HB.lock Definition cmd_disj_lock := cmd_disj.
Lemma cmd_disj_lockE : cmd_disj = cmd_disj_lock.
Proof. by rewrite cmd_disj_lock.unlock. Qed.
HB.lock Definition cmd_valid_lock := cmd_valid.
Lemma cmd_valid_lockE : cmd_valid = cmd_valid_lock.
Proof. by rewrite cmd_valid_lock.unlock. Qed.

Lemma cmd_var_disj_lock_skip T (x : qreg T) : cmd_var_disj_lock x skip_.
Proof. by rewrite -cmd_var_disj_lockE. Qed.

Lemma cmd_var_disj_lock_abort T (x : qreg T) : cmd_var_disj_lock x abort_.
Proof. by rewrite -cmd_var_disj_lockE. Qed.

Lemma cmd_var_disj_lock_init T1 T2 (x1 : qreg T1) (x2 : qreg T2) v : 
  disjoint_qreg x1 x2 -> cmd_var_disj_lock x1 (init_ x2 v).
Proof. by rewrite -cmd_var_disj_lockE. Qed.

Lemma cmd_var_disj_lock_unitary T1 T2 (x1 : qreg T1) (x2 : qreg T2) u : 
  disjoint_qreg x1 x2 -> cmd_var_disj_lock x1 (unitary_ x2 u).
Proof. by rewrite -cmd_var_disj_lockE. Qed.

(* Lemma cmd_var_disj_lock_cond2 T1 T2 (x1 : qreg T1) (x2 : qreg T2) M c0 c1 :
  disjoint_qreg x1 x2 -> cmd_var_disj_lock x1 c0 -> cmd_var_disj_lock x1 c1 ->
  cmd_var_disj_lock x1 (cond2_ x2 M c0 c1).
Proof. by rewrite -cmd_var_disj_lockE cond2_.unlock/==>->??; apply/forallP; case. Qed. *)

Lemma cmd_var_disj_lock_cond T1 T2 (F : finType) 
  (x1 : qreg T1) (x2 : qreg T2) M (f : F -> cmd_) :
  disjoint_qreg x1 x2 -> (forall i, cmd_var_disj_lock x1 (f i)) ->
  cmd_var_disj_lock x1 (cond_ x2 M f).
Proof. by rewrite -cmd_var_disj_lockE/==>->?; apply/forallP. Qed.

Lemma cmd_var_disj_lock_sequ T (x : qreg T) c1 c2 :
  cmd_var_disj_lock x c1 -> cmd_var_disj_lock x c2 ->
  cmd_var_disj_lock x (seqc_ c1 c2).
Proof. by rewrite -cmd_var_disj_lockE /==>->->. Qed.

Lemma cmd_var_disj_lock_while T1 T2 (x1 : qreg T1) (x2 : qreg T2) M b c :
  disjoint_qreg x1 x2 -> cmd_var_disj_lock x1 c ->
  cmd_var_disj_lock x1 (while_ x2 M b c).
Proof. by rewrite -cmd_var_disj_lockE /==>->->. Qed.

Lemma cmd_var_disj_lock_if T (x : qreg T) b u0 u1 :
  cmd_var_disj_lock x u0 -> cmd_var_disj_lock x u1 ->
    cmd_var_disj_lock x (if b then u0 else u1).
Proof. by case: b. Qed.

Lemma cmd_var_disj_lock_for (T : eqType) (r : seq T) (P : pred T) (fp : T -> cmd_) 
  I (x : qreg I) :
    (forall i, P i -> cmd_var_disj_lock x (fp i)) ->
      cmd_var_disj_lock x [for i <- r | P i do (fp i)].
Proof. rewrite cmd_var_disj_lock.unlock; exact: cmd_var_disj_for. Qed.

Ltac tac_cmd_var_disj := repeat match goal with
  | [ |- forall _ , _ ] => intros; 
          rewrite /= ?(eq_qreg_fst, eq_qreg_snd, eq_qreg_tuplei, eq_qreg_ffuni)/=
  | [ H : is_true (cmd_var_disj ?x ?y) |- is_true (cmd_var_disj_lock ?x ?y) ] => 
          rewrite -cmd_var_disj_lockE; apply H
  | [ H : is_true (cmd_var_disj_lock ?x ?y) |- is_true (cmd_var_disj_lock ?x ?y) ] => 
          apply H
  | [ |- is_true (cmd_var_disj_lock _ abort_)] => 
          apply/cmd_var_disj_lock_abort
  | [ |- is_true (cmd_var_disj_lock _ skip_)] => 
          apply/cmd_var_disj_lock_skip
  | [ |- is_true (cmd_var_disj_lock _ (init_ _ _))] => 
          apply/cmd_var_disj_lock_init
  | [ |- is_true (cmd_var_disj_lock _ (unitary_ _ _))] => 
          apply/cmd_var_disj_lock_unitary
  | [ |- is_true (cmd_var_disj_lock _ (seqc_ _ _))] => 
          apply/cmd_var_disj_lock_sequ
  | [ |- is_true (cmd_var_disj_lock _ (cond_ _ _ _))] => 
          apply/cmd_var_disj_lock_cond
  | [ |- is_true (cmd_var_disj_lock _ (while_ _ _ _))] => 
          apply/cmd_var_disj_lock_while
  | [ |- is_true (cmd_var_disj_lock _ (if _ then _ else _)) ] =>
          rewrite ?eqxx/=; try apply/cmd_var_disj_lock_if
  | [ |- is_true (cmd_var_disj_lock _ [for _ <- _ | _ do _]) ] =>
          apply/cmd_var_disj_lock_for
  | [ |- is_true (disjoint_qreg _ _) ] => QRegAuto.tac_expose
end.

Lemma cmd_disj_lock_abort c : cmd_disj_lock abort_ c.
Proof. by rewrite -cmd_disj_lockE. Qed.

Lemma cmd_disj_lock_skip c : cmd_disj_lock skip_ c.
Proof. by rewrite -cmd_disj_lockE. Qed.

Lemma cmd_disj_lock_init T (x : qreg T) v c : 
  cmd_var_disj_lock x c -> cmd_disj_lock (init_ x v) c.
Proof. by rewrite -cmd_disj_lockE/= -cmd_var_disj_lockE. Qed.

Lemma cmd_disj_lock_unitary T (x : qreg T) u c : 
  cmd_var_disj_lock x c -> cmd_disj_lock (unitary_ x u) c.
Proof. by rewrite -cmd_disj_lockE/= -cmd_var_disj_lockE. Qed.

(* Lemma cmd_disj_lock_cond2 T (x : qreg T) M c0 c1 c :
  cmd_var_disj_lock x c -> cmd_disj_lock c0 c -> cmd_disj_lock c1 c ->
    cmd_disj_lock (cond2_ x M c0 c1) c.
Proof. by rewrite -cmd_disj_lockE -cmd_var_disj_lockE cond2_.unlock/==>->??; apply/forallP; case. Qed. *)

Lemma cmd_disj_lock_cond T (F : finType) (x : qreg T) M (f : F -> cmd_) c :
  cmd_var_disj_lock x c -> (forall i, cmd_disj_lock (f i) c) ->
    cmd_disj_lock (cond_ x M f) c.
Proof. by rewrite -cmd_disj_lockE -cmd_var_disj_lockE/==>->?; apply/forallP. Qed.

Lemma cmd_disj_lock_sequ c1 c2 c :
  cmd_disj_lock c1 c -> cmd_disj_lock c2 c ->
  cmd_disj_lock (seqc_ c1 c2) c.
Proof. by rewrite -cmd_disj_lockE /==>->->. Qed.

Lemma cmd_disj_lock_while T (x : qreg T) M b c1 c :
  cmd_var_disj_lock x c -> cmd_disj_lock c1 c ->
  cmd_disj_lock (while_ x M b c1) c.
Proof. by rewrite -cmd_disj_lockE -cmd_var_disj_lockE/==>->->. Qed.

Lemma cmd_disj_lock_if b c0 c1 c :
  cmd_disj_lock c0 c -> cmd_disj_lock c1 c ->
    cmd_disj_lock (if b then c0 else c1) c.
Proof. by case: b. Qed.

Lemma cmd_disj_lockC c1 c2 : cmd_disj_lock c1 c2 = cmd_disj_lock c2 c1.
Proof. by rewrite -cmd_disj_lockE cmd_disjC. Qed.

Lemma cmd_disj_lock_for (T : eqType) (r : seq T) (P : pred T) (fp : T -> cmd_) c :
    (forall i, P i -> cmd_disj_lock (fp i) c) ->
      cmd_disj_lock [for i <- r | P i do (fp i)] c.
Proof. rewrite cmd_disj_lock.unlock; exact: cmd_disj_for. Qed.

Lemma cmd_disj_lock_forC (T : eqType) (r : seq T) (P : pred T) (fp : T -> cmd_) c :
    (forall i, P i -> cmd_disj_lock c (fp i)) ->
      cmd_disj_lock c [for i <- r | P i do (fp i)].
Proof. rewrite cmd_disj_lock.unlock; exact: cmd_disj_forC. Qed.

Ltac tac_cmd_disj := repeat match goal with
  | [ |- forall _ , _ ] => intros; 
          rewrite /= ?(eq_qreg_fst, eq_qreg_snd, eq_qreg_tuplei, eq_qreg_ffuni)/=
  | [ H : is_true (cmd_disj ?x ?y) |- is_true (cmd_disj_lock ?x ?y)] => 
          rewrite -cmd_disj_lockE; apply H
  | [ H : is_true (cmd_disj ?x ?y) |- is_true (cmd_disj_lock ?y ?x)] => 
          rewrite cmd_disj_lockC -cmd_disj_lockE; apply H
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
  | [ |- is_true (cmd_disj_lock (unitary_ _ _) _)] => 
          apply/cmd_disj_lock_unitary
  | [ |- is_true (cmd_disj_lock (seqc_ _ _) _)] => 
          apply/cmd_disj_lock_sequ
  | [ |- is_true (cmd_disj_lock (cond_ _ _ _) _)] => 
          apply/cmd_disj_lock_cond
  | [ |- is_true (cmd_disj_lock (while_ _ _ _) _)] => 
          apply/cmd_disj_lock_while
  | [ |- is_true (cmd_disj_lock (if _ then _ else _) _) ] =>
          rewrite ?eqxx/=; try apply/cmd_disj_lock_if
  | [ |- is_true (cmd_disj_lock [for _ <- _ | _ do _] _)] => 
          apply/cmd_disj_lock_for
  | [ |- is_true (cmd_disj_lock _ [for _ <- _ | _ do _])] => 
          apply/cmd_disj_lock_forC
  | [ |- is_true (cmd_var_disj_lock _ _) ] => tac_cmd_var_disj
end.

Lemma cmd_valid_lock_abort : cmd_valid_lock abort_.
Proof. by rewrite -cmd_valid_lockE. Qed.

Lemma cmd_valid_lock_skip : cmd_valid_lock skip_.
Proof. by rewrite -cmd_valid_lockE. Qed.

Lemma cmd_valid_lock_init T (x : qreg T) v : 
  valid_qreg x -> cmd_valid_lock (init_ x v).
Proof. by rewrite -cmd_valid_lockE. Qed.

Lemma cmd_valid_lock_unitary T (x : qreg T) u : 
  valid_qreg x -> cmd_valid_lock (unitary_ x u).
Proof. by rewrite -cmd_valid_lockE. Qed.

Lemma cmd_valid_lock_cond T (F : finType) (x : qreg T) M (f : F -> cmd_) :
  valid_qreg x -> (forall i, cmd_valid_lock (f i)) ->
    cmd_valid_lock (cond_ x M f).
Proof. by rewrite cmd_valid_lock.unlock/==>->/=/forallP. Qed.

Lemma cmd_valid_lock_sequ c1 c2 :
  cmd_valid_lock c1 -> cmd_valid_lock c2 ->
  cmd_valid_lock (seqc_ c1 c2).
Proof. by rewrite -cmd_valid_lockE /==>->->. Qed.

Lemma cmd_valid_lock_while T (x : qreg T) M b c :
  valid_qreg x -> cmd_valid_lock c ->
  cmd_valid_lock (while_ x M b c).
Proof. by rewrite -!cmd_valid_lockE/==>->->. Qed.

Lemma cmd_valid_lock_if b c0 c1 :
  cmd_valid c0 -> cmd_valid c1 ->
    cmd_valid (if b then c0 else c1).
Proof. by case: b. Qed.

Lemma cmd_valid_lock_for (T : eqType) (r : seq T) (P : pred T) (fp : T -> cmd_) :
    (forall i, P i -> cmd_valid_lock (fp i)) ->
      cmd_valid_lock [for i <- r | P i do (fp i)].
Proof. rewrite cmd_valid_lock.unlock; exact: cmd_valid_for. Qed.

Ltac tac_cmd_valid := repeat match goal with
  | [ |- forall _ , _ ] => intros; 
          rewrite /= ?(eq_qreg_fst, eq_qreg_snd, eq_qreg_tuplei, eq_qreg_ffuni)/=
  | [ H : is_true (cmd_valid ?x) |- is_true (cmd_valid_lock ?x) ] => apply H
  | [ H : is_true (cmd_valid_lock ?x) |- is_true (cmd_valid_lock ?x)] => 
          apply H
  | [ |- is_true (cmd_valid (cmd_base _)) ] => by apply/cmd_is_valid
  | [ |- is_true (cmd_valid_lock abort_)] => 
          apply/cmd_valid_lock_abort
  | [ |- is_true (cmd_valid_lock skip_)] => 
          apply/cmd_valid_lock_skip
  | [ |- is_true (cmd_valid_lock (init_ _ _))] => 
          apply/cmd_valid_lock_init
  | [ |- is_true (cmd_valid_lock (unitary_ _ _))] => 
          apply/cmd_valid_lock_unitary
  | [ |- is_true (cmd_valid_lock (seqc_ _ _))] => 
          apply/cmd_valid_lock_sequ
  | [ |- is_true (cmd_valid_lock (cond_ _ _ _))] => 
          apply/cmd_valid_lock_cond
  | [ |- is_true (cmd_valid_lock (while_ _ _ _))] => 
          apply/cmd_valid_lock_while
  | [ |- is_true (cmd_valid_lock (if _ then _ else _)) ] =>
          rewrite ?eqxx/=; try apply/cmd_valid_lock_if
  | [ |- is_true (cmd_valid_lock [for _ <- _ | _ do _])] => 
          apply/cmd_valid_lock_for
  | [ |- is_true (valid_qreg _)] => QRegAuto.tac_expose
end.

Ltac tac_disjoint_set_pre := repeat match goal with
  | [ |- forall _ , _ ] => intros 
  | [ |- is_true [disjoint _ (mset _) & _ (mset _)]] => rewrite -disj_setE
  | [ |- is_true [disjoint _ (mset _) & _ (fvars _)]] => apply/cmd_var_disjP
  | [ |- is_true [disjoint _ (fvars _) & _ (mset _)]] => 
        rewrite disjoint_sym; apply/cmd_var_disjP
  | [ |- is_true [disjoint _ (fvars _) & _ (fvars _)]] => apply/cmd_disjP
  | [ |- is_true (cmd_var_disj _ [for _ <- _ | _ do _]) ] => 
        apply/cmd_var_disj_for
  | [ |- is_true (cmd_disj _ [for _ <- _ | _ do _]) ] => apply/cmd_disj_for
  | [ |- is_true (cmd_disj [for _ <- _ | _ do _] _) ] => apply/cmd_disj_forC
  | [ |- is_true [disjoint _ (_ :|: _) & _]] => 
        rewrite disjointUX; apply/andP; split
  | [ |- is_true [disjoint _ & _ (_ :|: _)]] => 
        rewrite disjointXU; apply/andP; split
  | [ |- is_true [disjoint _ & _ (\bigcup_(_ | _) _)]] => try apply/bigcup_disjointP
  | [ |- is_true [disjoint _ (\bigcup_(_ | _) _) & _]] => 
      try (rewrite disjoint_sym; apply/bigcup_disjointP)
end.

Ltac tac_qwhile_auto := rewrite /cmd_expose;
  try tac_disjoint_set_pre;
  rewrite ?cmd_var_disj_lockE ?cmd_disj_lockE ?cmd_valid_lockE;
  rewrite /= ?(eq_qreg_fst, eq_qreg_snd, eq_qreg_tuplei, eq_qreg_ffuni)/=;
  repeat match goal with
  | [ H : ?x |- ?x ] => apply H
  | [ |- forall _ , _ ] => intros; 
          rewrite /= ?(eq_qreg_fst, eq_qreg_snd, eq_qreg_tuplei, eq_qreg_ffuni)/=
  | [ |- is_true (disjoint_qreg _ _)] => QRegAuto.tac_expose
  | [ |- is_true (valid_qreg _)] => QRegAuto.tac_expose
  | [ |- is_true (cmd_var_disj_lock _ _)] => tac_cmd_var_disj
  | [ |- is_true (cmd_disj_lock _ _)] => tac_cmd_disj
  | [ |- is_true (cmd_valid_lock _)] => tac_cmd_valid
  end.

Module Exports.
Global Hint Extern 0 (cmd_expose _) => (tac_qwhile_auto) : typeclass_instances.

(* Variable (T : qType) (x : 'QReg[T]) (v : 'NS('Ht T)) (U : 'FU('Ht T)).
Check [it x := v] ;; [ut x := U] : Cmd_. *)

End Exports.
End QWhileAuto.

