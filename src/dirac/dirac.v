(* -------------------------------------------------------------------- *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.analysis Require Import -(notations)forms.
From quantum.external Require Import spectral.
From mathcomp.classical Require Import boolp.
From mathcomp.analysis Require Import reals.
(* From mathcomp.real_closed Require Import complex. *)
From quantum.external Require Import complex.

Require Import mcextra mcaextra notation prodvect hermitian tensor.
Require Import mxpred extnum ctopology quantum.
From quantum.dirac Require Import setdec hstensor.

(*****************************************************************************)
(*                           Labelled Dirac Notation                         *)
(* This file provides a semantical implementation of labelled Dirac notation *)
(*   It is defined as a non-dependent variant type 'D of dffun.              *)
(*   'D has linear algebraic structure (with + and scalar *:)                *)
(* ------------------------------------------------------------------------- *)
(* implementation detail:                                                    *)
(*   'D[H] := forall i : {set L} * {set L}, 'F[H]_(i.1, i.2)                 *)
(*   for any (e : 'D) and (S,T : {set L}),                                   *)
(*          e S T return the linear function 'F[H]_(S,T)                     *)
(*   for any S T (f :'F[H]_(S,T)), '[ f ] return a 'D                        *)
(* ------------------------------------------------------------------------- *)
(*   operations on 'D :                                                      *)
(*          construct : ket '|v>, bra '<v|, lin '[f], numd %:D               *)
(*          (inverse)     d2v       d2dv      d2f       d2c                  *)
(*          unary: adjoint ^A, conjugate ^C, transpose ^T                    *)
(*          binary: comp \o, tensor \⊗, general comp \·                     *)
(*                                                                           *)
(*   operation consistent : e.g., '[ f \⊗ g ] = '[ f ] \⊗ '[ g ]           *)
(*                                                                           *)
(*   big op :                                                                *)
(*          \mul : for comp    \o;  Monoid: Law, MulLaw, AddLaw              *)
(*          \ten_s : for tensor \⊗;  Monoid: Law, MulLaw, ComLaw AddLaw     *)
(*          \dot  : for dot     \·;  Monoid: MulLaw, AddLaw                  *)
(* ------------------------------------------------------------------------- *)
(*   tracing domain/codomain by using Canonical structure mechanism :        *)
(*                                                                           *)
(*          structure : 'D_(S,T) : e = '[ f ] for some f : 'F[H]_(S,T)       *)
(*          structure : 'D_S  : e = '[ f ] for some f : 'F[H]_S              *)
(*          structure : 'Ket_S  : e = '|v> for some v : 'H[H]_S              *)
(*          structure : {bar S}  : e = '<v| for some v : 'H[H]_S             *)
(*                                                                           *)
(*      canonical structure of each operations on 'D                         *)
(*          check [sqr of e | S] : find if e is canonical to 'D_S            *)
(* ------------------------------------------------------------------------- *)
(*      onbdType := structure type of orthonormal basis f : F -> 'D_S        *)
(*                  similar to onbType                                       *)
(*                  The HB class is ONBDirac                                 *)
(*      nsdType := structure type of normalized states                       *)
(*                  similar to nsType                                        *)
(*                  The HB class is NSDirac                                  *)
(* ------------------------------------------------------------------------- *)
(*   vorder of Dirac : e1 ⊑ e2 iff forall S T, 0 ⊑ (e2-e1) S S              *)
(*                                  & (e2-e1) S T = 0 if (S != T)            *)
(*****************************************************************************)

(* ------------------------------------------------------------------------- *)
Import Order.TTheory GRing.Theory Num.Theory Num.Def.

(* ------------------------------------------------------------------------- *)
Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

(* ------------------------------------------------------------------------- *)
Local Open Scope set_scope.
Local Open Scope efnd_scope.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Notation C := hermitian.C.

(* ------------------------------------------------------------------------- *)
Import VectorInternalTheory.

Declare Scope dirac_scope.

Section DiracDef.
Variable L : finType.
Variable H : L -> chsType.

Variant dirac : predArgType := 
  Dirac of {dffun forall d : {set L} * {set L}, 'F[H]_(d.1,d.2)}.

Definition dirac_val u := let: Dirac t := u in t.

HB.instance Definition _ := [isNew for dirac_val].

Definition fun_of_dirac u (i : {set L}) (j : {set L}) : 'F_(i,j) := dirac_val u (i,j).
Coercion fun_of_dirac : dirac >-> Funclass.

HB.instance Definition _ := [Choice of dirac by <:].

End DiracDef.

Fact dirac_key : unit. Proof. by []. Qed.
HB.lock 
Definition dirac_of_fun (L : finType) (H : L -> chsType) (k : unit) 
  (F : forall (i j : {set L}), 'F[H]_(i,j)) := 
    @Dirac L H [ffun i => F i.1 i.2].
Canonical dirac_unlockable := Unlockable dirac_of_fun.unlock.

Section DiracDef2.
Variable L : finType.
Variable H : L -> chsType.
Implicit Type F : forall (i j : {set L}), 'F[H]_(i,j).

Lemma diracE k F i j : dirac_of_fun k F i j = F i j.
Proof. by rewrite [dirac_of_fun]unlock /fun_of_dirac /= ffunE. Qed.

Lemma diracP (u v : dirac H) : (forall i j, u i j = v i j) <-> u = v.
Proof.
rewrite /fun_of_dirac; split=> [/= eq_uv | -> //].
by apply/val_inj/ffunP=> [[i j]]; apply: eq_uv.
Qed.

Lemma eq_dirac k F1 F2 : (forall i j, F1 i j = F2 i j) ->
  dirac_of_fun k F1 = dirac_of_fun k F2.
Proof. by move=> eq_uv; apply/diracP => i j; rewrite !diracE eq_uv. Qed.

End DiracDef2.

Delimit Scope dirac_scope with D.
Bind Scope dirac_scope with dirac.
Local Open Scope dirac_scope.
Notation "''D[' H ]" := (@dirac _ H) (only parsing) : type_scope.
Notation "''D'" := (@dirac _ _) : type_scope.
Notation "\dirac_ ( i , j ) E" := (dirac_of_fun dirac_key (fun i j => E%VF)) : dirac_scope.

(* Dirac : ringType with + and tensor (!!not com)*)
(* Dirac : vectType, so we can talk about its completeness, but not used now *)
Section DiracAlgebra.
Context {L : finType} {H : L -> chsType}.
Implicit Types u v w : 'D[H].

Definition dirac_zero     := \dirac_(i , j) (0 : 'F[H]_(i,j)).
Definition dirac_add  u v := \dirac_(i , j) (u i j + v i j).
Definition dirac_opp  u   := \dirac_(i , j) - u i j.
Definition dirac_scale (c : C) u := \dirac_(i , j) (c *: u i j).

Program Definition dirac_zmodMixin := @GRing.isZmodule.Build 'D[H]
  dirac_zero dirac_opp dirac_add _ _ _ _.
Next Obligation.
by move=> f g h; apply/diracP=> i j; rewrite !diracE addrA.
Qed.
Next Obligation.
by move=> f g; apply/diracP=> i j; rewrite !diracE addrC.
Qed.
Next Obligation.
by move=> f; apply/diracP=> i j; rewrite !diracE add0r.
Qed.
Next Obligation.
by move=> f; apply/diracP=> i j; rewrite !diracE addNr.
Qed.
HB.instance Definition _ := dirac_zmodMixin.

Lemma dirac_sumE T (r : seq T) (P : pred T) (F : T -> 'D[H]) i j :
  (\sum_(x <- r | P x) F x) i j = \sum_(x <- r | P x) F x i j.
Proof. by elim/big_rec2: _ => /= [|x _ s Px <-]; rewrite diracE. Qed.

Program Definition dirac_lmodMixin := @GRing.Zmodule_isLmodule.Build C 'D[H]
  dirac_scale _ _ _ _.
Next Obligation.
by move=> /= c d x; apply/diracP=> i j; rewrite !diracE scalerA.
Qed.
Next Obligation.
by move=> /= x; apply/diracP=> i j; rewrite !diracE scale1r.
Qed.
Next Obligation.
by move=> /= c u v; apply/diracP=> i j; rewrite !diracE scalerDr.
Qed.
Next Obligation.
by move=> /= u c d; apply/diracP=> i j; rewrite !diracE scalerDl.
Qed.
HB.instance Definition _ := dirac_lmodMixin.

(* Lemma dirac_valZ c f i : dirac_val (c *: f) i = c *: dirac_val f i.
Proof. by rewrite {1}/GRing.scale/=/dirac_scale unlock/= ffunE; case: i. Qed.
Lemma dirac_valD f g i : dirac_val (f + g) i = dirac_val f i + dirac_val g i.
Proof. by rewrite {1}/GRing.add/=/dirac_add unlock/= ffunE; case: i. Qed.
Lemma dirac_valN f i : dirac_val (- f) i = - dirac_val f i.
Proof. by rewrite {1}/GRing.opp/=/dirac_opp unlock/= ffunE; case: i. Qed.
Lemma dirac_val0 i : dirac_val 0 i = 0.
Proof. by rewrite{1}/GRing.zero/=/dirac_zero/=unlock/= ffunE. Qed. *)

Let D := (\sum_i dim 'F[H]_(i.1,i.2))%N.
Lemma dirac_vect_iso : Vector.axiom D 'D.
Proof.
pose Z := {i : {set L} * {set L} & 'I_(dim 'F[H]_(i.1,i.2))}.
pose S (i : {set L} * {set L}) (x : 'I_(dim 'F[H]_(i.1,i.2))) : Z := Tagged _ x.
suff: Vector.axiom #|{: Z}| 'D.
- apply: vect_axiom_eqdim; rewrite /D card_tagged.
  rewrite sumnE big_map big_enum /=.
  by apply: eq_bigr=> i _; rewrite card_ord.
pose fr (f : 'D) := \row_(i < #|{: Z}|)
  v2r (dirac_val f (tag (enum_val i))) 0 (tagged (enum_val i)).
exists fr=> /= [c f g|].
- apply/rowP=> i; rewrite !mxE {1}/GRing.scale/=/dirac_scale/= {1}/GRing.add/=
  /dirac_add dirac_of_fun.unlock/= ffunE/= /fun_of_dirac/= ffunE/= linearP/= !mxE.
  congr (c * (v2r _) 0 (tagged (enum_val i)) + (v2r _) 0 (tagged (enum_val i)));
  by case: (tag (enum_val i)).
pose gr (i : {set L} * {set L}) (x : 'rV[C]_#|{: Z}|) :=
  r2v (\row_(j < dim 'F[H]_(i.1,i.2)) x 0 (enum_rank (S _ j))).
exists (fun x => Dirac [ffun i => gr i x]) => [g|r].
- apply/val_inj=>/=; apply/ffunP=>i; rewrite ffunE /fr /gr.
  set r := (X in r2v X); suff ->: r = v2r (dirac_val g i) by rewrite v2rK.
  by apply/rowP=> k; rewrite !mxE enum_rankK /=.
- apply/rowP=> j; rewrite !mxE /= ffunE /gr r2vK mxE; congr (_ _ _).
  by apply/(canLR enum_valK)/esym/eqP; rewrite eq_Tagged.
Qed.
HB.instance Definition _ := Lmodule_hasFinDim.Build _ 'D[H]
  dirac_vect_iso.

End DiracAlgebra.

(* We define the basic constructors *)
(* lind ketd brad numd conjd trd adjd muld dotd tend *)
(* we prevent any possible unfolding of them *)
HB.lock 
Definition lind {L : finType} {H : L -> chsType} [S T] (f: 'F[H]_(S,T)) : 'D[H] := 
  \dirac_(i,j)
    match S =P i , T =P j return 'F[H]_(i,j) with
    | ReflectT eqi, ReflectT eqj => castlf (eqi, eqj) f
    | _, _ => 0
    end.
HB.lock
Definition ketd {L : finType} {H : L -> chsType} [S] (v : 'H[H]_S) : 'D[H] := lind (v2f v).
HB.lock
Definition brad {L : finType} {H : L -> chsType} [S] (v : 'H[H]_S) : 'D[H] := lind (v2df v).
HB.lock
Definition numd {L : finType} {H : L -> chsType} (c : C) : 'D[H] := lind (s2sf c).
HB.lock
Definition conjd {L : finType} {H : L -> chsType} (e : 'D[H]) : 'D[H] := \dirac_(i,j) (e i j)^C.
HB.lock
Definition trd   {L : finType} {H : L -> chsType} (e : 'D[H]) : 'D[H] := \dirac_(i,j) (e j i)^T.
HB.lock
Definition adjd  {L : finType} {H : L -> chsType} (e : 'D[H]) : 'D[H] := \dirac_(i,j) (e j i)^A.
HB.lock
Definition muld  {L : finType} {H : L -> chsType} (e1 e2 : 'D[H]) : 'D[H] :=
  \dirac_(i , j) \sum_(k : {set L}) (e1 k j \o e2 i k : 'F[H]_(i,j)).
HB.lock
Definition dotd  {L : finType} {H : L -> chsType} (e1 e2 : 'D[H]) : 'D[H] := 
  \sum_d11 \sum_d12 \sum_d21 \sum_d22 lind (e1 d11 d12 \· e2 d21 d22).
HB.lock
Definition tend  {L : finType} {H : L -> chsType} (e1 e2 : 'D[H]) : 'D[H] := 
  \sum_d11 \sum_d12 \sum_d21 \sum_d22 lind (e1 d11 d12 \⊗ e2 d21 d22).

Fact tends_key : unit. Proof. by []. Qed.
Fact dotds_key : unit. Proof. by []. Qed.
Definition bigtend {L : finType} {H : L -> chsType} := locked_with tends_key (@idfun 'D[H]).
Definition bigdotd {L : finType} {H : L -> chsType} := locked_with dotds_key (@idfun 'D[H]).
Lemma bigtend_unfold {L : finType} {H : L -> chsType} : @bigtend L H = id.
Proof. by rewrite /bigtend unlock. Qed.
Lemma bigdotd_unfold {L : finType} {H : L -> chsType} : @bigdotd L H = id.
Proof. by rewrite /bigdotd unlock. Qed.
Definition bigd := (@bigtend_unfold, @bigdotd_unfold). 

HB.lock 
Definition d2v {L : finType} {H : L -> chsType} S (e : 'D[H]) : 'H[H]_S := f2v (e set0 S).
HB.lock 
Definition d2dv {L : finType} {H : L -> chsType} S (e : 'D[H]) : 'H[H]_S := df2v (e S set0).
HB.lock 
Definition d2f {L : finType} {H : L -> chsType} S T (e : 'D[H]) : 'F[H]_(S,T) := e S T.
HB.lock 
Definition d2c {L : finType} {H : L -> chsType} (e : 'D[H]) := sf2s (e set0 set0).

Notation "':1'"  := (@numd _ _ 1) : dirac_scope.
Notation "c %:D" := (@numd _ _ c) : dirac_scope.
Notation "'| v >" := (@ketd _ _ _ v%VF) : dirac_scope.
Notation "'< v |"  := (@brad _ _ _ v%VF) : dirac_scope.
Notation "'[ M ]"   := (@lind _ _ _ _ M%VF) : dirac_scope.
Notation "'\1_' S" := (@lind _ _ S%SET S%SET \1) : dirac_scope.
Notation "e '^C'" := (conjd e) : dirac_scope.
Notation "e '^T'" := (trd e) : dirac_scope.
Notation "e '^A'" := (adjd e) : dirac_scope.
Notation " 'o%D' "  := (@muld _ _) : function_scope.
Notation " '·%D' "  := (@dotd _ _) : function_scope.
Notation " '⊗%D' " := (@tend _ _) : function_scope.
Notation " f '\o' g "  := (muld f g) : dirac_scope.
Notation " f '\⊗' g " := (tend f g) : dirac_scope.
Notation " f '\·' g "  := (dotd f g) : dirac_scope.

Notation "\ten_ ( i <- r | P ) F" :=
  (bigtend (\big[ ⊗%D / :1 ]_(i <- r | P%B) F%D )) : dirac_scope.
Notation "\ten_ ( i <- r ) F" :=
  (bigtend (\big[ ⊗%D / :1 ]_(i <- r) F%D)) : dirac_scope.
Notation "\ten_ ( m <= i < n | P ) F" :=
  (bigtend ((\big[ ⊗%D / :1 ]_( m%N <= i < n%N | P%B) F%D)%BIG)) 
    : dirac_scope.
Notation "\ten_ ( m <= i < n ) F" :=
  (bigtend ((\big[ ⊗%D / :1 ]_(m%N <= i < n%N) F%D)%BIG)) : dirac_scope.
Notation "\ten_ ( i | P ) F" :=
  (bigtend (\big[ ⊗%D / :1 ]_(i | P%B) F%D)) : dirac_scope.
Notation "\ten_ i F" :=
  (bigtend (\big[ ⊗%D / :1 ]_i F%D)) : dirac_scope.
Notation "\ten_ ( i : t | P ) F" :=
  (bigtend (\big[ ⊗%D / :1 ]_(i : t | P%B) F%D)) (only parsing) 
    : dirac_scope.
Notation "\ten_ ( i : t ) F" :=
  (bigtend (\big[ ⊗%D / :1 ]_(i : t) F%D)) (only parsing) : dirac_scope.
Notation "\ten_ ( i < n | P ) F" :=
  (bigtend ((\big[ ⊗%D / :1 ]_(i < n%N | P%B) F%D)%BIG)) : dirac_scope.
Notation "\ten_ ( i < n ) F" :=
  (bigtend ((\big[ ⊗%D / :1 ]_(i < n%N) F%D)%BIG)) : dirac_scope.
Notation "\ten_ ( i 'in' A | P ) F" :=
  (bigtend (\big[ ⊗%D / :1 ]_(i in A | P%B) F%D)) : dirac_scope.
Notation "\ten_ ( i 'in' A ) F" :=
  (bigtend (\big[ ⊗%D / :1 ]_(i in A) F%D)) : dirac_scope.

Notation "\dot_ ( i <- r | P ) F" :=
  (bigdotd (\big[ ·%D / :1 ]_(i <- r | P%B) F%D )) : dirac_scope.
Notation "\dot_ ( i <- r ) F" :=
  (bigdotd (\big[ ·%D / :1 ]_(i <- r) F%D)) : dirac_scope.
Notation "\dot_ ( m <= i < n | P ) F" :=
  (bigdotd ((\big[ ·%D / :1 ]_( m%N <= i < n%N | P%B) F%D)%BIG)) 
    : dirac_scope.
Notation "\dot_ ( m <= i < n ) F" :=
  (bigdotd ((\big[ ·%D / :1 ]_(m%N <= i < n%N) F%D)%BIG)) : dirac_scope.
Notation "\dot_ ( i | P ) F" :=
  (bigdotd (\big[ ·%D / :1 ]_(i | P%B) F%D)) : dirac_scope.
Notation "\dot_ i F" :=
  (bigdotd (\big[ ·%D / :1 ]_i F%D)) : dirac_scope.
Notation "\dot_ ( i : t | P ) F" :=
  (bigdotd (\big[ ·%D / :1 ]_(i : t | P%B) F%D)) (only parsing) 
    : dirac_scope.
Notation "\dot_ ( i : t ) F" :=
  (bigdotd (\big[ ·%D / :1 ]_(i : t) F%D)) (only parsing) : dirac_scope.
Notation "\dot_ ( i < n | P ) F" :=
  (bigdotd ((\big[ ·%D / :1 ]_(i < n%N | P%B) F%D)%BIG)) : dirac_scope.
Notation "\dot_ ( i < n ) F" :=
  (bigdotd ((\big[ ·%D / :1 ]_(i < n%N) F%D)%BIG)) : dirac_scope.
Notation "\dot_ ( i 'in' A | P ) F" :=
  (bigdotd (\big[ ·%D / :1 ]_(i in A | P%B) F%D)) : dirac_scope.
Notation "\dot_ ( i 'in' A ) F" :=
  (bigdotd (\big[ ·%D / :1 ]_(i in A) F%D)) : dirac_scope.

Section DiracBigLock.
Context {L : finType} (H : L -> chsType).

Lemma bigtendlr (I J : Type) (ri : seq I) (Pi : pred I) (Fi : I -> 'D[H]) 
  (rj : seq J) (Pj : pred J) (Fj : J -> 'D): 
    bigtend ((\big[⊗%D/:1]_(i <- ri | Pi i) Fi i) \⊗
    (\big[@tend _ _ /:1]_(j <- rj | Pj j) Fj j)) = 
    (\ten_(i <- ri | Pi i) Fi i) \⊗ (\ten_(j <- rj | Pj j) Fj j) .
Proof. by rewrite bigd. Qed.

Lemma bigtendr (I : Type) (r : seq I) (P : pred I) (e1 : 'D[H]) (F : I -> 'D): 
  bigtend (e1 \⊗ (\big[⊗%D/:1]_(j <- r | P j) F j)) = e1 \⊗ (\ten_(i <- r | P i) F i).
Proof. by rewrite bigd. Qed.

Lemma bigtendl (I : Type) (r : seq I) (P : pred I) (e1 : 'D[H]) (F : I -> 'D[H]): 
  bigtend ((\big[⊗%D/:1]_(j <- r | P j) F j) \⊗ e1) = (\ten_(i <- r | P i) F i) \⊗ e1.
Proof. by rewrite bigd. Qed.

Lemma bigtendE (I : Type) (r : seq I) (P : pred I) (F : I -> 'D[H]): 
  \big[⊗%D/:1]_(j <- r | P j) F j = \ten_(i <- r | P i) F i.
Proof. by rewrite bigd. Qed.

Lemma bigdotdlr (I J : Type) (ri : seq I) (Pi : pred I) (Fi : I -> 'D[H]) 
  (rj : seq J) (Pj : pred J) (Fj : J -> 'D[H]): 
  bigdotd (dotd (\big[·%D/:1]_(i <- ri | Pi i) Fi i) 
  (\big[·%D/:1]_(j <- rj | Pj j) Fj j)) = 
  (\dot_(i <- ri | Pi i) Fi i) \· (\dot_(j <- rj | Pj j) Fj j) .
Proof. by rewrite bigd. Qed.

Lemma bigdotdr (I : Type) (r : seq I) (P : pred I) (e1 : 'D[H]) (F : I -> 'D[H]): 
  bigdotd (dotd e1 (\big[·%D/:1]_(j <- r | P j) F j)) = dotd e1 (\dot_(i <- r | P i) F i).
Proof. by rewrite bigd. Qed.

Lemma bigdotdl (I : Type) (r : seq I) (P : pred I) (e1 : 'D[H]) (F : I -> 'D[H]): 
  bigdotd (dotd (\big[·%D/:1]_(j <- r | P j) F j) e1) = dotd (\dot_(i <- r | P i) F i) e1.
Proof. by rewrite bigd. Qed.

Lemma bigdotdE (I : Type) (r : seq I) (P : pred I) (F : I -> 'D[H]): 
  \big[·%D/:1]_(j <- r | P j) F j = \dot_(i <- r | P i) F i.
Proof. by rewrite bigd. Qed.

Definition bigd_lock := (bigtendE, bigdotdE).

Definition bigdE := (bigtendlr, bigtendr, bigtendl, bigdotdlr, bigdotdr, bigdotdl).
End DiracBigLock.

(* after using bigop theory, first run this to lock back *)
(* Ltac bigdE := rewrite ?bigd; rewrite ?bigd_locklr. *)
(* move *)
Lemma exchange_bigR (R : Type) (idx : R) (op : Monoid.com_law idx) 
  (I J K : Type) (rI : seq I) (rJ : seq J) (rK : seq K) (P : pred I) 
    (Q : pred J) (S : pred K) (F : I -> J -> K -> R) : 
    \big[op/idx]_(i <- rI | P i) \big[op/idx]_(j <- rJ | Q j) 
        \big[op/idx]_(k <- rK | S k) F i j k = \big[op/idx]_(j <- rJ | Q j) 
            \big[op/idx]_(k <- rK | S k) \big[op/idx]_(i <- rI | P i) F i j k.
Proof. by rewrite exchange_big; apply eq_bigr=>i Pi; apply exchange_big. Qed.

Section DiracOpCorrect.
Context {L : finType} {H : L -> chsType}.

Lemma lind_cast S T S' T' (eqST: (S = S') * (T = T')) (f: 'F[H]_(S,T)) :
  lind (castlf eqST f) = lind f.
Proof. by case: eqST => eqS eqT; case: S' / eqS; case: T' / eqT; rewrite castlf_id. Qed. 
Lemma ketd_cast S S' (eqS : S = S') (v : 'H[H]_S) :
  '| casths eqS v > = '| v >.
Proof. by case: S' / eqS; rewrite casths_id. Qed.
Lemma brad_cast S S' (eqS : S = S') (v : 'H[H]_S) :
  '< casths eqS v | = '< v |.
Proof. by case: S' / eqS; rewrite casths_id. Qed.

Lemma lind_id S T (f : 'F[H]_(S,T)) : lind f S T = f.
Proof. by rewrite lind.unlock diracE; (do 2 case: eqP=>//?); rewrite castlf_id. Qed.
Lemma lind_eq0l S T S' T' (f : 'F[H]_(S,T)) :
  S' != S -> lind f S' T' = 0.
Proof. by rewrite eq_sym lind.unlock diracE; case: eqP. Qed.
Lemma lind_eq0r S T S' T' (f : 'F[H]_(S,T)) :
  T' != T -> lind f S' T' = 0.
Proof. by rewrite eq_sym lind.unlock diracE; do 2 case: eqP=>//. Qed.
Lemma lind_eq0p S T S' T' (f : 'F[H]_(S,T)) :
  (S',T') != (S,T) -> lind f S' T' = 0.
Proof.
rewrite xpair_eqE negb_and=>/orP[P|P].
by rewrite lind_eq0l. by rewrite lind_eq0r.
Qed.

Lemma lindK S T : cancel (@lind _ H S T) (@d2f _ H S T).
Proof. by move=>f; rewrite d2f.unlock lind_id. Qed.
Lemma lind_inj S T : injective (@lind L H S T).
Proof. exact: (can_inj (@lindK S T)). Qed.
Lemma ketdK S : cancel (@ketd _ H S) (@d2v _ H S).
Proof. by move=>f; rewrite ketd.unlock d2v.unlock lind_id v2fK. Qed.
Lemma ketd_inj S : injective (@ketd _ H S).
Proof. exact: (can_inj (@ketdK S)). Qed.
Lemma bradK S : cancel (@brad _ H S) (@d2dv _ H S).
Proof. by move=>f; rewrite brad.unlock d2dv.unlock lind_id v2dfK. Qed.
Lemma brad_inj S : injective (@brad _ H S).
Proof. exact: (can_inj (@bradK S)). Qed.
Lemma numdK : cancel (@numd _ H) (@d2c _ H).
Proof. by move=>f; rewrite numd.unlock d2c.unlock lind_id s2sfK. Qed.
Lemma numd_inj : injective (@numd _ H).
Proof. exact: (can_inj (@numdK)). Qed.

Lemma lind_is_linear S T : linear (@lind _ H S T).
Proof.
move=>a x y; apply/diracP=>i j; rewrite lind.unlock !diracE.
case: eqP=>p1; first case: eqP=>p2;
by rewrite ?linearP// scaler0 addr0.
Qed.
HB.instance Definition _ S T := GRing.isLinear.Build C 
  'F[H]_(S,T) 'D[H] *:%R (@lind _ H S T) (@lind_is_linear S T).

Lemma ketd_is_linear S : linear (@ketd _ H S).
Proof. by move=>a x y; rewrite ketd.unlock !linearP. Qed.
HB.instance Definition _ S := GRing.isLinear.Build C 
  'H[H]_S 'D[H] *:%R (@ketd _ H S) (@ketd_is_linear S).

Lemma brad_is_antilinear S : linear_for (Num.conj_op \; *:%R) (@brad _ H S).
Proof. by move=>a x y; rewrite brad.unlock !linearP. Qed.
HB.instance Definition _ S := GRing.isLinear.Build C 
  'H[H]_S 'D[H] (Num.conj_op \; *:%R) (@brad _ H S) (@brad_is_antilinear S).

Lemma numd_is_additive : additive (@numd _ H).
Proof. by move=>x y; rewrite numd.unlock raddfB linearB. Qed.
HB.instance Definition _ := GRing.isAdditive.Build C
  'D[H] (@numd _ H) numd_is_additive.

Lemma d2f_is_linear S T : linear (@d2f _ H S T).
Proof. by move=>a x y; rewrite d2f.unlock !diracE. Qed.
HB.instance Definition _ S T := GRing.isLinear.Build C 
  'D[H] 'F[H]_(S,T) *:%R (@d2f _ H S T) (@d2f_is_linear S T).

Lemma d2v_is_linear S : linear (@d2v _ H S).
Proof. by move=>a x y; rewrite d2v.unlock !diracE linearP. Qed.
HB.instance Definition _ S := GRing.isLinear.Build C 
  'D[H] 'H[H]_S *:%R (@d2v _ H S) (@d2v_is_linear S).

Lemma d2dv_is_antilinear S : linear_for (Num.conj_op \; *:%R) (@d2dv _ H S).
Proof. by move=>a x y; rewrite d2dv.unlock !diracE linearP. Qed.
HB.instance Definition _ S := GRing.isLinear.Build C 
  'D[H] 'H[H]_S (Num.conj_op \; *:%R) (@d2dv _ H S) (@d2dv_is_antilinear S).

Lemma d2c_is_scalar : scalar (@d2c _ H).
Proof. by move=>a x y; rewrite d2c.unlock !diracE linearP. Qed.
HB.instance Definition _ S := GRing.isLinear.Build C 
  'D[H] C *%R (@d2c _ H) d2c_is_scalar.

Lemma lind_dec (f : 'D[H]) : \sum_i lind (f i.1 i.2) = f.
Proof.
by apply/diracP=>i j; rewrite dirac_sumE (bigD1 (i,j))// big1/=
  =>[[k1 k2]/= nk|]; rewrite ?addr0 ?lind_id// lind_eq0p// eq_sym.
Qed.

(* correctness of compoistion operators *)
Lemma addd_correct S T (f g: 'F[H]_(S,T)) :
  '[f] + '[g] = '[f + g].
Proof. by rewrite linearD. Qed.

Lemma oppd_correct S T (f : 'F[H]_(S,T)) : 
  - '[f] = '[- f].
Proof. by rewrite linearN. Qed.

Lemma scaled_correct S T (c: C) (f : 'F[H]_(S,T)) :
  c *: '[f] = '[c *: f].
Proof. by rewrite linearZ. Qed.

Definition comp_lfun0 := (comp_lfun0l, comp_lfun0r).

Lemma muld_correct S T W (f: 'F[H]_(S,T)) (g: 'F_(W,S)) :
    '[f] \o '[g] = '[f \o g].
Proof.
apply/diracP=>d1 d2; rewrite muld.unlock [LHS]diracE.
rewrite (bigD1 S)//= big1=>[i P|].
by rewrite lind_eq0l ?comp_lfun0l.
case E: (d1 == W); last by rewrite ![_ d1 _]lind_eq0l ?E// comp_lfun0r addr0.
case E1: (d2 == T); last by rewrite/= ![_ _ _ d2]lind_eq0r ?E1// comp_lfun0l addr0.
move: E E1=>/eqP->/eqP->; by rewrite !lind_id addr0.
Qed.

Lemma tend_pairE (e1 e2 : 'D[H]) : 
  e1 \⊗ e2 = \sum_d1 \sum_d2 lind (e1 d1.1 d1.2 \⊗ e2 d2.1 d2.2).
Proof. by rewrite tend.unlock pair_big; apply eq_bigr=>d1 _; rewrite pair_big. Qed.

Lemma dotd_pairE (e1 e2 : 'D[H]) : 
  e1 \· e2 = \sum_d1 \sum_d2 lind (e1 d1.1 d1.2 \· e2 d2.1 d2.2).
Proof. by rewrite dotd.unlock pair_big; apply eq_bigr=>d1 _; rewrite pair_big. Qed.

Lemma tend_correct S T S' T' (f: 'F[H]_(S,T)) (g: 'F_(S', T')) :
    '[f] \⊗ '[g] = '[f \⊗ g].
Proof.
apply/diracP=>d1 d2; rewrite tend_pairE.
rewrite (bigD1 (S,T))//= (bigD1 (S',T'))//= !big1=>[[i1 i2]/=P|[i1 i2]/=P|].
by rewrite [lind g _ _]lind_eq0p// tenf0 linear0.
by rewrite big1=>[j _|]; rewrite 1?lind_eq0p// ?ten0f ?linear0// diracE.
by rewrite !addr0 !lind_id.
Qed.

Lemma dotd_correct S T S' T' (f: 'F[H]_(S,T)) (g: 'F[H]_(S', T')) :
    '[f] \· '[g] = '[f \· g].
Proof.
apply/diracP=>d1 d2; rewrite dotd_pairE. 
rewrite (bigD1 (S,T))//= (bigD1 (S',T'))//= !big1=>[[i1 i2]/=P|[i1 i2]/=P|]. 
by rewrite [lind g _ _]lind_eq0p// dotf0 linear0.
by rewrite big1=>[j _|]; rewrite 1?lind_eq0p// ?dot0f ?linear0// diracE.
by rewrite !addr0 !lind_id.
Qed.

Lemma sdotd_correct S T (f: 'F[H]_S) (g: 'F[H]_T) :
  '[f] \· '[g] = '[f \O g].
Proof. by rewrite sdot_lfun.unlock lind_cast dotd_correct. Qed.

Lemma conjd_correct S T (f : 'F[H]_(S,T)) :
  '[f]^C = '[f^C].
Proof.
apply/diracP=>i j; rewrite conjd.unlock diracE.
case E: ((i,j) == (S,T)); first by move/eqP in E; inversion E; rewrite !lind_id.
by move/negbT: E=>E; rewrite !lind_eq0p// linear0.
Qed.

Lemma adjd_correct S T (f : 'F[H]_(S,T)) :
  '[f]^A = '[f^A].
Proof.
apply/diracP=>i j; rewrite adjd.unlock diracE.
case E: ((i,j) == (T,S)); first by move/eqP in E; inversion E; rewrite !lind_id.
move/negbT: E=>E; rewrite !lind_eq0p// ?linear0//.
by move: E; apply contraNN=>/eqP P; inversion P.
Qed.

Lemma trd_correct S T (f : 'F[H]_(S,T)) :
  '[f]^T = '[f^T].
Proof.
apply/diracP=>i j; rewrite trd.unlock diracE.
case E: ((i,j) == (T,S)); first by move/eqP in E; inversion E; rewrite !lind_id.
move/negbT: E=>E; rewrite !lind_eq0p// ?linear0//.
by move: E; apply contraNN=>/eqP P; inversion P.
Qed.

Definition dirac_correct := (addd_correct, oppd_correct, 
  scaled_correct, muld_correct, tend_correct, dotd_correct, 
  conjd_correct, adjd_correct, trd_correct ).

Lemma lind_eqFnd S T S' T' (f: 'F[H]_(S,T)) (g: 'F_(S',T')) :
  f =c g -> lind f = lind g.
Proof. by move=>P; move: (eq_FndP P); rewrite !to_FndK=><-; rewrite lind_cast. Qed.

Lemma ketd_eqHnd S S' (f: 'H[H]_S) (g: 'H_S') :
  f =v g -> ketd f = ketd g.
Proof. by move=>Pe; move: (eq_Hnd1 Pe)=>/= Pv; case: _ / Pv g Pe => g /to_Hnd_inj ->. Qed.

Lemma brad_eqHnd S S' (f: 'H[H]_S) (g: 'H_S') :
  f =v g -> brad f = brad g.
Proof. by move=>Pe; move: (eq_Hnd1 Pe)=>/= Pv; case: _ / Pv g Pe => g /to_Hnd_inj ->. Qed.

End DiracOpCorrect.

Ltac to_Fnd := try (match goal with
  | [ |- lind _ = lind _ ] => apply/lind_eqFnd
  | [ |- ketd _ = ketd _ ] => apply/ketd_eqHnd
  | [ |- brad _ = brad _ ] => apply/brad_eqHnd
  | [ |- _ ] => apply/to_Fnd_inj
  | [ |- _ ] => apply/to_Hnd_inj
  end); rewrite ?(to_FndE, Fnd_cast, to_Fnd_tens, to_HndE, Hnd_cast, to_Hnd_tens).

(* we locally use ringType (+ , \⊗) to ease the proof of theorems *)
Section DiracTheory.
Context {L : finType} (H : L -> chsType).
Implicit Type (e x y z: 'D[H]) (a b c : C) (S T : {set L}).

Local Notation "c %:D" := (@numd _ H c).
Local Notation "⊗%D" := (@tend _ H) : function_scope.
Local Notation "o%D"  := (@muld _ H) : function_scope.
Local Notation "·%D" := (@dotd _ H) : function_scope.
Local Notation ":1" := (@numd _ H 1).
Local Notation conjd := (@conjd _ H).
Local Notation trd := (@trd _ H).
Local Notation adjd := (@adjd _ H).

Lemma ketd_lin S (v : 'H[H]_S) : '| v > = '[v2f v].
Proof. by rewrite ketd.unlock. Qed.
Lemma brad_lin S (v : 'H[H]_S) : '< v | = '[v2df v].
Proof. by rewrite brad.unlock. Qed.
Lemma lind_ket S (f : 'FV[H]_S) : '[f] = '|f2v f>.
Proof. by rewrite ketd_lin f2vK. Qed.
Lemma lind_bra S (f : 'FdV[H]_S) : '[f] = '<df2v f|.
Proof. by rewrite brad_lin df2vK. Qed.
Lemma lind_num (f : 'F[H]_set0) : '[f] = (sf2s f)%:D.
Proof. by rewrite numd.unlock sf2sK. Qed.
Lemma ketd_num (v : 'H[H]_set0) : '|v> = (sv2s v)%:D.
Proof.
rewrite ketd.unlock numd.unlock; f_equal; apply/lfunPD=>i.
by rewrite v2fE /s2sf/sv2s [v]dec_sv idx0E linearZr/= dv_dot eqxx scale1r lfunE/= lfunE/= mulr1.
Qed.
Lemma brad_num (v : 'H[H]_set0) : '<v| = (sv2s v)^*%:D.
Proof. by rewrite brad_lin -v2f_adj sfAC v2f_conj -ketd_lin ketd_num sv2s_conj. Qed.
Lemma numd_lin c : c%:D = '[s2sf c].
Proof. by rewrite lind_num s2sfK. Qed.
Lemma numd_ket c : c%:D = '|s2sv c>.
Proof. by rewrite ketd_num s2svK. Qed.
Lemma numd_bra c : c%:D = '<s2sv c^*|.
Proof. by rewrite brad_num s2svK conjCK. Qed.

Lemma numd1I : :1 = \1_set0.
Proof. by rewrite numd.unlock lind.unlock; f_equal; rewrite /s2sf scale1r. Qed.
Locate "⊗%D".
Lemma tendA : associative ⊗%D.
Proof.
move=>f g h; rewrite !tend_pairE [RHS]exchange_big/=.
rewrite  (eq_bigr (fun d1 => \sum_d0 \sum_d3 \sum_d2
 lind (f d1.1 d1.2 \⊗ (lind (g d0.1 d0.2 \⊗ h d3.1 d3.2) d2.1 d2.2)))).
2: rewrite  [RHS](eq_bigr (fun j => \sum_d1 \sum_d2 \sum_i
(lind (lind (f d1.1 d1.2 \⊗ g d2.1 d2.2) i.1 i.2 \⊗ h j.1 j.2)))).
1,2: by move=>i _; rewrite exchange_bigR/= exchange_bigR/=; apply eq_bigr=>j _;
rewrite dirac_sumE 1 ?linear_suml/= 2 ?linear_sum/=; apply eq_bigr=>k _;
rewrite dirac_sumE 1 ?linear_suml/= 2 ?linear_sum/=; apply eq_bigr.
rewrite [RHS]exchange_bigR/=; apply eq_bigr=>[[i1 i2]] _; 
apply eq_bigr=>[[j1 j2]] _; apply eq_bigr=>[[k1 k2]] _.
rewrite (bigD1 (j1 :|: k1, j2 :|: k2))// big1/=.
2: rewrite (bigD1 (i1 :|: j1, i2 :|: j2))// big1/=.
1,2 : by move=>[l1 l2]/=nl; rewrite lind_eq0p// ?tenf0 ?ten0f linear0.
by rewrite !lind_id !addr0; to_Fnd; rewrite tenFA.
Qed.

Lemma tendC : commutative ⊗%D.
Proof.
move=>f g. rewrite 2 !tend_pairE exchange_big/=.
apply eq_bigr=>[[i1 i2]] _; apply eq_bigr=>[[j1 j2]] _/=.
by to_Fnd; rewrite tenFC.
Qed.

Lemma ten1d : left_id :1 ⊗%D.
Proof.
move=>f. rewrite tend_pairE (bigD1 (set0,set0))//= [X in _ + X]big1/=.
move=>[i1 i2]/= ni0. rewrite big1// =>? _/=.
by rewrite numd1I lind_eq0p// ten0f linear0.
rewrite addr0 -[RHS]lind_dec; apply eq_bigr=>i _.
by rewrite numd1I lind_id; to_Fnd; rewrite ten1F.
Qed.

Lemma tend1 : right_id :1 ⊗%D.
Proof. by move=>f; rewrite tendC ten1d. Qed.

Lemma linear_tend f : linear (⊗%D f).
Proof.
move=>a v w. rewrite !tend_pairE linear_sum -big_split/=; apply eq_bigr=>i _/=.
rewrite linear_sum -big_split; apply eq_bigr=>j _/=.
by rewrite !diracE !linearP/=.
Qed.
HB.instance Definition _ f := GRing.isLinear.Build 
  C 'D[H] 'D[H] *:%R (@tend _ H f) (@linear_tend f).
Lemma linear_tendr f : linear ((@tend _ H)^~ f).
Proof. by move=>a v w; rewrite tendC linearP/= ![f \⊗ _]tendC. Qed.
HB.instance Definition _ := bilinear_isBilinear.Build C 'D[H] 'D[H] 'D[H]
  *:%R *:%R (@tend _ H) (linear_tendr, linear_tend).

Lemma tendAC x y z : x \⊗ y \⊗ z = x \⊗ z \⊗ y.
Proof. by rewrite -tendA [y \⊗ z]tendC tendA. Qed.
Lemma tendCA x y z : x \⊗ (y \⊗ z) = y \⊗ (x \⊗ z).
Proof. by rewrite tendC tendAC -tendA. Qed.
Lemma tendACA x y z t : x \⊗ y \⊗ (z \⊗ t) = x \⊗ z \⊗ (y \⊗ t).
Proof. by rewrite -!tendA (tendCA y). Qed.

Lemma ten0d : left_zero 0 ⊗%D. Proof. exact: linear0l. Qed.
Lemma tend0 : right_zero 0 ⊗%D. Proof. exact: linear0r. Qed.
Lemma tendDl : left_distributive ⊗%D +%R. 
Proof. by move=>x y z; rewrite linearDl. Qed.
Lemma tendDr : right_distributive ⊗%D +%R.
Proof. by move=>x y z; rewrite linearD. Qed.
Lemma tendN x y : x \⊗ (- y) = - (x \⊗ y). Proof. exact: raddfN. Qed.
Lemma tendN1 x : x \⊗ -:1 = - x. Proof. by rewrite tendN tend1. Qed.
Lemma tendBr z : {morph ⊗%D z : x y / x - y}. Proof. exact: raddfB. Qed.
Lemma tendMnr z n : {morph ⊗%D z : x / x *+ n}. Proof. exact: raddfMn. Qed.
Definition tendnAr := tendMnr.
Lemma tendMNnr z n : {morph ⊗%D z : x / x *- n}. Proof. exact: raddfMNn. Qed.
Lemma tend_sumr z I r (P : pred I) E :
  z \⊗ (\sum_(i <- r | P i) E i) = \sum_(i <- r | P i) (z \⊗ E i).
Proof. exact: raddf_sum. Qed.
Lemma tendZr z a : {morph ⊗%D z : x / a *: x}. Proof. exact: linearZ. Qed.
Lemma tendPr z a : {morph ⊗%D z : u v / a *: u + v}. Proof. exact: linearP. Qed.
Lemma tenNd x y : (- x) \⊗ y = - (x \⊗ y). Proof. exact: linearNl. Qed.
Lemma tenN1d x : -:1 \⊗ x = - x. Proof. by rewrite tenNd ten1d. Qed.
Lemma tendNN x y : (- x) \⊗ (- y) = x \⊗ y. Proof. by rewrite tendN tenNd opprK. Qed.
Lemma tendBl z : {morph ⊗%D^~ z : x y / x - y}. Proof. exact: linearBl. Qed.
Lemma tendMnl z n : {morph ⊗%D^~ z : x / x *+ n}. Proof. exact: linearMnl. Qed.
Definition tendnAl := tendMnl.
Lemma tendMNnl z n : {morph ⊗%D^~ z : x / x *- n}. Proof. exact: linearMNnl. Qed.
Lemma tend_suml z I r (P : pred I) E :
  (\sum_(i <- r | P i) E i) \⊗ z = \sum_(i <- r | P i) (E i \⊗ z).
Proof. exact: linear_suml. Qed.
Lemma tendZl z a : {morph ⊗%D^~ z : x / a *: x}. Proof. exact: linearZl_LR. Qed.
Lemma tendPl z a : {morph ⊗%D^~ z : u v / a *: u + v}. Proof. exact: linearPl. Qed.
Lemma tendZlr x y a b : (a *: x) \⊗ (b *: y) = a *: (b *: (x \⊗ y)). 
Proof. exact: linearZlr. Qed.
Lemma tendZrl x y a b : (a *: x) \⊗ (b *: y) = b *: (a *: (x \⊗ y)). 
Proof. exact: linearZrl. Qed.

Lemma oned_neq0 : (:1 : 'D[H]) != 0.
Proof.
apply/eqP=> /diracP/(_ set0 set0)/eqP.
by rewrite numd1I lind_id diracE (@oner_eq0 ('F[H]_set0 : ringType)).
Qed.

Definition tend_comRingMixin :=
  GRing.Zmodule_isComRing.Build 'D[H] tendA tendC ten1d tendDl oned_neq0.
Definition tend_ringType : ringType := 
  HB.pack 'D[H] tend_comRingMixin.

Lemma muldA : associative o%D.
Proof.
move=>x y z; rewrite muld.unlock.
apply/diracP=>i j; rewrite !diracE.
under eq_bigr do rewrite !diracE linear_sumr/=.
rewrite exchange_big/=. apply eq_bigr=>k _.
rewrite diracE/= linear_suml/=. 
by under eq_bigr do rewrite comp_lfunA.
Qed.

Lemma linear_muld f : linear (o%D f).
Proof.
move=>a v w; apply/diracP=>i j; rewrite muld.unlock.
rewrite !diracE !linear_sum/= -big_split; apply eq_bigr=>k _/=.
by rewrite !diracE linearPr/=.
Qed.
HB.instance Definition _ f := GRing.isLinear.Build 
  C 'D[H] 'D[H] *:%R (@muld _ H f) (@linear_muld f).
Lemma linear_muldr f : linear ((@muld _ H)^~ f).
Proof.
move=>a v w; apply/diracP=>i j; rewrite muld.unlock.
rewrite !diracE !linear_sum/= -big_split; apply eq_bigr=>k _/=.
by rewrite !diracE linearPl/=.
Qed.
HB.instance Definition _ := bilinear_isBilinear.Build C 'D[H] 'D[H] 'D[H]
  *:%R *:%R (@muld _ H) (linear_muldr, linear_muld).

Lemma mul0d : left_zero 0 o%D. Proof. exact: linear0l. Qed.
Lemma muld0 : right_zero 0 o%D. Proof. exact: linear0r. Qed.
Lemma muldDl : left_distributive o%D +%R. 
Proof. by move=>x y z; rewrite linearDl. Qed.
Lemma muldDr : right_distributive o%D +%R.
Proof. by move=>x y z; rewrite linearD. Qed.
Lemma muldN x y : x \o (- y) = - (x \o y). Proof. exact: raddfN. Qed.
Lemma muldBr z : {morph o%D z : x y / x - y}. Proof. exact: raddfB. Qed.
Lemma muldMnr z n : {morph o%D z : x / x *+ n}. Proof. exact: raddfMn. Qed.
Definition muldnAr := muldMnr.
Lemma muldMNnr z n : {morph o%D z : x / x *- n}. Proof. exact: raddfMNn. Qed.
Lemma muld_sumr z I r (P : pred I) E :
  z \o (\sum_(i <- r | P i) E i) = \sum_(i <- r | P i) (z \o E i).
Proof. exact: raddf_sum. Qed.
Lemma muldZr z a : {morph o%D z : x / a *: x}. Proof. exact: linearZ. Qed.
Lemma muldPr z a : {morph o%D z : u v / a *: u + v}. Proof. exact: linearP. Qed.
Lemma mulNd x y : (- x) \o y = - (x \o y). Proof. exact: linearNl. Qed.
Lemma muldNN x y : (- x) \o (- y) = x \o y. Proof. by rewrite muldN mulNd opprK. Qed.
Lemma muldBl z : {morph o%D^~ z : x y / x - y}. Proof. exact: linearBl. Qed.
Lemma muldMnl z n : {morph o%D^~ z : x / x *+ n}. Proof. exact: linearMnl. Qed.
Definition muldnAl := muldMnl.
Lemma muldMNnl z n : {morph o%D^~ z : x / x *- n}. Proof. exact: linearMNnl. Qed.
Lemma muld_suml z I r (P : pred I) E :
  (\sum_(i <- r | P i) E i) \o z = \sum_(i <- r | P i) (E i \o z).
Proof. exact: linear_suml. Qed.
Lemma muldZl z a : {morph o%D^~ z : x / a *: x}. Proof. exact: linearZl_LR. Qed.
Lemma muldPl z a : {morph o%D^~ z : u v / a *: u + v}. Proof. exact: linearPl. Qed.
Lemma muldZlr x y a b : (a *: x) \o (b *: y) = a *: (b *: (x \o y)). 
Proof. exact: linearZlr. Qed.
Lemma muldZrl x y a b : (a *: x) \o (b *: y) = b *: (a *: (x \o y)). 
Proof. exact: linearZrl. Qed.

Lemma dot1d : left_id :1 ·%D.
Proof.
move=>f; rewrite dotd_pairE (bigD1 (set0,set0))//= [X in _ + X]big1/==>[[i1 i2] ni0|].
by rewrite big1// =>j _; rewrite /= numd1I lind_eq0p// dot0f linear0.
rewrite addr0 -[RHS]lind_dec; apply eq_bigr=>[[i1 i2]] _/=.
by to_Fnd; rewrite numd1I lind_id dot1F.
Qed.

Lemma dotd1 : right_id :1 ·%D.
Proof.
move=>f; rewrite dotd_pairE exchange_big (bigD1 (set0,set0))//= 
  [X in _ + X]big1/==>[[i1 i2] ni0|].
by rewrite big1// =>j _; rewrite /= numd1I lind_eq0p// dotf0 linear0.
rewrite addr0 -[RHS]lind_dec; apply eq_bigr=>[[i1 i2]] _/=.
by to_Fnd; rewrite numd1I lind_id dotF1.
Qed.

Lemma linear_dotd f : linear (·%D f).
Proof.
move=>a v w; rewrite !dotd_pairE linear_sum -big_split; apply eq_bigr=>i _/=.
rewrite linear_sum -big_split; apply eq_bigr=>j _/=.
by rewrite !diracE !linearP/=.
Qed.
HB.instance Definition _ f := GRing.isLinear.Build 
  C 'D[H] 'D[H] *:%R (@dotd _ H f) (@linear_dotd f).
Lemma linear_dotdr f : linear ((@dotd _ H)^~ f).
Proof.
move=>a v w; rewrite !dotd_pairE linear_sum -big_split; apply eq_bigr=>i _/=.
rewrite linear_sum -big_split; apply eq_bigr=>j _/=.
by rewrite !diracE !(linearP,linearPl)/=.
Qed.
HB.instance Definition _ := bilinear_isBilinear.Build C 'D[H] 'D[H] 'D[H]
  *:%R *:%R (@dotd _ H) (linear_dotdr, linear_dotd).

Lemma dot0d : left_zero 0 ·%D. Proof. exact: linear0l. Qed.
Lemma dotd0 : right_zero 0 ·%D. Proof. exact: linear0r. Qed.
Lemma dotdDl : left_distributive ·%D +%R. 
Proof. by move=>x y z; rewrite linearDl. Qed.
Lemma dotdDr : right_distributive ·%D +%R.
Proof. by move=>x y z; rewrite linearD. Qed.
Lemma dotdN x y : x \· (- y) = - (x \· y). Proof. exact: raddfN. Qed.
Lemma dotdN1 x : x \· -:1 = - x. Proof. by rewrite dotdN dotd1. Qed.
Lemma dotdBr z : {morph ·%D z : x y / x - y}. Proof. exact: raddfB. Qed.
Lemma dotdMnr z n : {morph ·%D z : x / x *+ n}. Proof. exact: raddfMn. Qed.
Definition dotdnAr := dotdMnr.
Lemma dotdMNnr z n : {morph ·%D z : x / x *- n}. Proof. exact: raddfMNn. Qed.
Lemma dotd_sumr z I r (P : pred I) E :
  z \· (\sum_(i <- r | P i) E i) = \sum_(i <- r | P i) (z \· E i).
Proof. exact: raddf_sum. Qed.
Lemma dotdZr z a : {morph ·%D z : x / a *: x}. Proof. exact: linearZ. Qed.
Lemma dotdPr z a : {morph ·%D z : u v / a *: u + v}. Proof. exact: linearP. Qed.
Lemma dotNd x y : (- x) \· y = - (x \· y). Proof. exact: linearNl. Qed.
Lemma dotN1d x : -:1 \· x = - x. Proof. by rewrite dotNd dot1d. Qed.
Lemma dotdNN x y : (- x) \· (- y) = x \· y. Proof. by rewrite dotdN dotNd opprK. Qed.
Lemma dotdBl z : {morph ·%D^~ z : x y / x - y}. Proof. exact: linearBl. Qed.
Lemma dotdMnl z n : {morph ·%D^~ z : x / x *+ n}. Proof. exact: linearMnl. Qed.
Definition dotdnAl := dotdMnl.
Lemma dotdMNnl z n : {morph ·%D^~ z : x / x *- n}. Proof. exact: linearMNnl. Qed.
Lemma dotd_suml z I r (P : pred I) E :
  (\sum_(i <- r | P i) E i) \· z = \sum_(i <- r | P i) (E i \· z).
Proof. exact: linear_suml. Qed.
Lemma dotdZl z a : {morph ·%D^~ z : x / a *: x}. Proof. exact: linearZl_LR. Qed.
Lemma dotdPl z a : {morph ·%D^~ z : u v / a *: u + v}. Proof. exact: linearPl. Qed.
Lemma dotdZlr x y a b : (a *: x) \· (b *: y) = a *: (b *: (x \· y)). 
Proof. exact: linearZlr. Qed.
Lemma dotdZrl x y a b : (a *: x) \· (b *: y) = b *: (a *: (x \· y)). 
Proof. exact: linearZrl. Qed.

Lemma conjd_is_antilinear : linear_for (Num.conj_op \; *:%R) conjd.
Proof. by move=>a x y/=; apply/diracP=>i j; rewrite conjd.unlock !diracE linearP. Qed.
HB.instance Definition _ := GRing.isLinear.Build 
  C 'D[H] 'D[H] (Num.conj_op \; *:%R) conjd conjd_is_antilinear.
Lemma adjd_is_antilinear  : linear_for (Num.conj_op \; *:%R) adjd.
Proof. by move=>a x y/=; apply/diracP=>i j; rewrite adjd.unlock !diracE linearP. Qed.
HB.instance Definition _ := GRing.isLinear.Build 
  C 'D[H] 'D[H] (Num.conj_op \; *:%R) adjd adjd_is_antilinear.
Lemma trd_is_linear  : linear trd.
Proof. by move=>a x y/=; apply/diracP=>i j; rewrite trd.unlock !diracE linearP. Qed.
HB.instance Definition _ := GRing.isLinear.Build 
  C 'D[H] 'D[H] *:%R trd trd_is_linear.

Lemma conjd0 : 0^C = (0 : 'D[H]). Proof. exact: linear0. Qed.
Lemma conjdN : {morph conjd : x / - x}. Proof. exact: linearN. Qed.
Lemma conjdD : {morph conjd : x y / x + y}. Proof. exact: linearD. Qed.
Lemma conjdB : {morph conjd : x y / x - y}. Proof. exact: linearB. Qed.
Lemma conjdMn n : {morph conjd : x / x *+ n}. Proof. exact: linearMn. Qed.
Lemma conjdMNn n : {morph conjd : x / x *- n}. Proof. exact: linearMNn. Qed.
Lemma conjd_sum I r (P : pred I) (E : I -> 'D[H]) :
  (\sum_(i <- r | P i) E i)^C = \sum_(i <- r | P i) (E i)^C.
Proof. exact: linear_sum. Qed.
Lemma conjdZ a : {morph conjd : x / a *: x >-> a^* *: x}. Proof. exact: linearZ. Qed.
Lemma conjdP a : {morph conjd : x y / a *: x + y >-> a^* *: x + y}.
Proof. exact: linearP. Qed.
Lemma conjdI S : (\1_S : 'D[H])^C = \1_S.
Proof. by rewrite conjd_correct conjf1. Qed.
Lemma conjd1 : :1^C = (:1 : 'D[H]).
Proof. by rewrite numd1I conjd_correct conjf1. Qed.
Lemma conjdN1 : (-:1)^C = (-:1 : 'D[H]).
Proof. by rewrite conjdN conjd1. Qed.
Lemma conjdK : involutive conjd.
Proof. by move=>x; apply/diracP=>i j; rewrite conjd.unlock !diracE conjfK. Qed.
Lemma conjd_inj : injective conjd.
Proof. exact: (can_inj conjdK). Qed.
Lemma conjd_lin S T (f : 'F[H]_(S,T)) : '[f]^C = '[f^C].
Proof. by rewrite conjd_correct. Qed.
Lemma conjd_ket S (v : 'H[H]_S) : '|v>^C = '|v^*v>.
Proof. by rewrite !ketd_lin conjd_lin v2f_conj. Qed.
Lemma conjd_bra S (v : 'H[H]_S) : '<v|^C = '<v^*v|.
Proof. by rewrite !brad_lin conjd_lin v2df_conj. Qed.
Lemma conjd_num c : c%:D^C = c^*%:D.
Proof. by rewrite !numd_lin conjd_lin s2sf_conj. Qed.
Lemma conjdM e1 e2 : (e1 \o e2)^C = e1^C \o e2^C.
Proof.
apply/diracP=>i j; rewrite conjd.unlock muld.unlock !diracE linear_sum/=.
by apply eq_bigr=>s _; rewrite conjf_comp !diracE.
Qed.
Lemma conjdT e1 e2 : (e1 \⊗ e2)^C = e1^C \⊗ e2^C.
Proof.
rewrite -(lind_dec e1) -(lind_dec e2) tend_suml !conjd_sum tend_suml.
apply eq_bigr=>??; rewrite !tend_sumr conjd_sum; apply eq_bigr=>??. 
by rewrite !dirac_correct tenf_conj.
Qed.
Lemma conjdG e1 e2 : (e1 \· e2)^C = e1^C \· e2^C.
Proof.
rewrite -(lind_dec e1) -(lind_dec e2) dotd_suml !conjd_sum dotd_suml.
apply eq_bigr=>??; rewrite !dotd_sumr conjd_sum; apply eq_bigr=>??. 
by rewrite !dirac_correct dotf_conj.
Qed.

Lemma adjd0 : 0^A = (0 : 'D[H]). Proof. exact: linear0. Qed.
Lemma adjdN : {morph adjd : x / - x}. Proof. exact: linearN. Qed.
Lemma adjdD : {morph adjd : x y / x + y}. Proof. exact: linearD. Qed.
Lemma adjdB : {morph adjd : x y / x - y}. Proof. exact: linearB. Qed.
Lemma adjdMn n : {morph adjd : x / x *+ n}. Proof. exact: linearMn. Qed.
Lemma adjdMNn n : {morph adjd : x / x *- n}. Proof. exact: linearMNn. Qed.
Lemma adjd_sum I r (P : pred I) (E : I -> 'D[H]) :
  (\sum_(i <- r | P i) E i)^A = \sum_(i <- r | P i) (E i)^A.
Proof. exact: linear_sum. Qed.
Lemma adjdZ a : {morph adjd : x / a *: x >-> a^* *: x}. Proof. exact: linearZ. Qed.
Lemma adjdP a : {morph adjd : x y / a *: x + y >-> a^* *: x + y}.
Proof. exact: linearP. Qed.
Lemma adjdI S : (\1_S : 'D[H])^A = \1_S.
Proof. by rewrite adjd_correct adjf1. Qed.
Lemma adjd1 : :1^A = (:1 : 'D[H]).
Proof. by rewrite !numd1I adjd_correct adjf1. Qed.
Lemma adjdN1 : (-:1)^A = (-:1 : 'D[H]).
Proof. by rewrite adjdN adjd1. Qed.
Lemma adjdK : involutive adjd.
Proof. by move=>x; apply/diracP=>i j; rewrite adjd.unlock !diracE adjfK. Qed.
Lemma adjd_inj : injective adjd.
Proof. exact: (can_inj adjdK). Qed.
Lemma adjd_lin S T (f : 'F[H]_(S,T)) : '[f]^A = '[f^A].
Proof. by rewrite adjd_correct. Qed.
Lemma adjd_ket S (v : 'H[H]_S) : '|v>^A = '<v|.
Proof. by rewrite ketd_lin adjd_lin v2f_adj brad_lin. Qed.
Lemma adjd_bra S (v : 'H[H]_S) : '<v|^A = '|v>.
Proof. by rewrite ketd_lin brad_lin adjd_lin v2df_adj. Qed.
Lemma adjd_num c : c%:D^A = c^*%:D.
Proof. by rewrite !numd_lin adjd_lin s2sf_adj. Qed.
Lemma adjdM e1 e2 : (e1 \o e2)^A = e2^A \o e1^A.
Proof.
apply/diracP=>i j. rewrite adjd.unlock muld.unlock !diracE linear_sum/=.
by apply eq_bigr=>s _; rewrite adjf_comp !diracE.
Qed.
Lemma adjdT e1 e2 : (e1 \⊗ e2)^A = e1^A \⊗ e2^A.
Proof.
rewrite -(lind_dec e1) -(lind_dec e2) tend_suml !adjd_sum tend_suml.
apply eq_bigr=>??; rewrite !tend_sumr adjd_sum; apply eq_bigr=>??. 
by rewrite !dirac_correct tenf_adj.
Qed.
Lemma adjdG e1 e2 : (e1 \· e2)^A = e2^A \· e1^A.
Proof.
rewrite -(lind_dec e1) -(lind_dec e2) dotd_suml !adjd_sum dotd_sumr.
apply eq_bigr=>??; rewrite dotd_sumr dotd_suml adjd_sum; apply eq_bigr=>??.
by rewrite !dirac_correct dotf_adj.
Qed.

Lemma trdAC e : e^T = e^A^C.
Proof. by apply/diracP=>i j; rewrite trd.unlock adjd.unlock conjd.unlock !diracE trfAC. Qed.
Lemma trd0 : 0^T = (0 : 'D[H]). Proof. exact: linear0. Qed.
Lemma trdN : {morph trd : x / - x}. Proof. exact: linearN. Qed.
Lemma trdD : {morph trd : x y / x + y}. Proof. exact: linearD. Qed.
Lemma trdB : {morph trd : x y / x - y}. Proof. exact: linearB. Qed.
Lemma trdMn n : {morph trd : x / x *+ n}. Proof. exact: linearMn. Qed.
Lemma trdMNn n : {morph trd : x / x *- n}. Proof. exact: linearMNn. Qed.
Lemma trd_sum I r (P : pred I) (E : I -> 'D[H]) :
  (\sum_(i <- r | P i) E i)^T = \sum_(i <- r | P i) ((E i)^T)%D.
Proof. exact: linear_sum. Qed.
Lemma trdZ a : {morph trd : x / a *: x}. Proof. exact: linearZ. Qed.
Lemma trdP a : {morph trd : x y / a *: x + y}. Proof. exact: linearP. Qed.
Lemma trdI S : (\1_S : 'D[H])^T = \1_S.
Proof. by rewrite trd_correct trf1. Qed.
Lemma trd1 : :1^T = (:1 : 'D[H]).
Proof. by rewrite numd1I trd_correct sfT. Qed.
Lemma trdN1 : (-:1)^T = (-:1 : 'D[H]).
Proof. by rewrite trdN trd1. Qed.
Lemma trdK : involutive trd.
Proof. by move=>x; apply/diracP=>i j; rewrite trd.unlock !diracE trfK. Qed.  
Lemma trd_inj : injective trd.
Proof. exact: (can_inj trdK). Qed.
Lemma trdM e1 e2 : (e1 \o e2)^T = e2^T \o e1^T.
Proof. by rewrite !trdAC adjdM conjdM. Qed.
Lemma trdT e1 e2 : (e1 \⊗ e2)^T = e1^T \⊗ e2^T.
Proof. by rewrite !trdAC adjdT conjdT. Qed.
Lemma trdG e1 e2 : (e1 \· e2)^T = e2^T \· e1^T.
Proof. by rewrite !trdAC adjdG conjdG. Qed.
Lemma trd_lin S T (f : 'F[H]_(S,T)) : '[f]^T = '[f^T].
Proof. by rewrite trd_correct. Qed.
Lemma trd_ket S (v : 'H[H]_S) : '|v>^T = '<v^*v|.
Proof. by rewrite trdAC adjd_ket conjd_bra. Qed.
Lemma trd_bra S (v : 'H[H]_S) : '<v|^T = '|v^*v>.
Proof. by rewrite trdAC adjd_bra conjd_ket. Qed.
Lemma trd_num c : c%:D^T = c%:D.
Proof. by rewrite trdAC adjd_num conjd_num conjCK. Qed.

Lemma dACC e : e^A^C = e^C^A.
Proof. by apply/diracP=>i j; rewrite adjd.unlock conjd.unlock !diracE lfACC. Qed.
Lemma trdCA   e : e^T = e^C^A. Proof. by rewrite trdAC dACC. Qed.
Lemma conjdAT e : e^C = e^A^T. Proof. by rewrite trdAC adjdK. Qed.
Lemma conjdTA e : e^C = e^T^A. Proof. by rewrite trdCA adjdK. Qed.
Lemma adjdTC  e : e^A = e^T^C. Proof. by rewrite trdAC conjdK. Qed.
Lemma adjdCT  e : e^A = e^C^T. Proof. by rewrite trdCA conjdK. Qed.
Definition dT2AC := trdAC.
Definition dT2CA := trdCA.
Definition dC2AT := conjdAT.
Definition dC2TA := conjdTA.
Definition dA2TC := adjdTC.
Definition dA2CT := adjdCT.
Lemma dCAC e : e^C^A = e^A^C. Proof. by rewrite dACC. Qed.
Lemma dATC e : e^A^T = e^T^A. Proof. by rewrite -dC2AT dC2TA. Qed.
Lemma dTAC e : e^T^A = e^A^T. Proof. by rewrite dATC. Qed.
Lemma dTCC e : e^T^C = e^C^T. Proof. by rewrite -dA2TC dA2CT. Qed.
Lemma dCTC e : e^C^T = e^T^C. Proof. by rewrite dTCC. Qed.

Lemma lind0 S T : '[0 : 'F[H]_(S,T)] = 0.
Proof. by rewrite linear0. Qed.
Lemma ketd0 S : '| (0 : 'H[H]_S) > = 0.
Proof. by rewrite linear0. Qed.
Lemma brad0 S : '< (0 : 'H[H]_S) | = 0.
Proof. by rewrite linear0. Qed.

(* recommend: write from numd -> c *)
Lemma lindI1 : \1_set0 = :1.
Proof. by rewrite numd1I. Qed.
Lemma lindI1_cond S : S = set0 -> \1_S = :1.
Proof. by move=>->; rewrite lindI1. Qed.
Lemma numd0 : 0%:D = 0. Proof. by rewrite raddf0. Qed.
Lemma numdN a : -a%:D = (-a)%:D. Proof. by rewrite raddfN. Qed.
Lemma numdD a b : a%:D + b%:D = (a+b)%:D. Proof. by rewrite raddfD. Qed.
Lemma numdB a b : a%:D - b%:D = (a-b)%:D. Proof. by rewrite raddfB. Qed.
Lemma numdMn n a : a%:D*+n = (a*+n)%:D. Proof. by rewrite raddfMn. Qed.
Lemma numdMNn n a : a%:D*-n = (a*-n)%:D. Proof. by rewrite raddfMNn. Qed.
Lemma numd_sum I r (P : pred I) (E : I -> C) :
  \sum_(i <- r | P i) (E i)%:D = (\sum_(i <- r | P i) E i)%:D.
Proof. by rewrite raddf_sum. Qed.
Lemma numdZ a b : a*:b%:D = (a*b)%:D.
Proof. by rewrite numd.unlock /s2sf -!linearZ/= scalerA mulrC. Qed.
Lemma numdZ1 a : a%:D = a *: :1. Proof. by rewrite numdZ mulr1. Qed.
Lemma numdP a b c : a*:b%:D + c%:D= (a*b+c)%:D.
Proof. by rewrite numdZ numdD. Qed.
Lemma numdTl x a : a%:D \⊗ x = a *: x. 
Proof. by rewrite numdZ1 tendZl ten1d. Qed.
Lemma numdTr x a : x \⊗ a%:D = a *: x. 
Proof. by rewrite tendC numdTl. Qed.
Lemma numdT a b : a%:D \⊗ b%:D = (a*b)%:D. 
Proof. by rewrite numdTl numdZ. Qed.
Lemma numdM a b : a%:D \o b%:D = (a*b)%:D. 
Proof. by rewrite !numd_lin muld_correct /s2sf -comp_lfunZl -comp_lfunZr scalerA comp_lfun1r. Qed.
Lemma numdGl x a : a%:D \· x = a *: x. 
Proof. by rewrite numdZ1 dotdZl dot1d. Qed.
Lemma numdGr x a : x \· a%:D = a *: x. 
Proof. by rewrite numdZ1 dotdZr dotd1. Qed.
Lemma numdG a b : a%:D \· b%:D = (a*b)%:D. 
Proof. by rewrite numdGl numdZ. Qed.
Definition numd_adj := adjd_num.

Definition numd_linear := (numd0, numd1I, numdN, numdD, numdB, numdMn, numdMNn, numd_sum, numdZ, numdP).
Definition numd_simp := (ketd_num, brad_num, lind_num, adjd_num, conjd_num, trd_num, 
  numdTl, numdTr, numdT, numdM, numdGl, numdGr, numdG).

End DiracTheory.

Section DiracBig.
Context {L : finType} (H : L -> chsType).
(* since generally we need to import GRing.Theory, *)
(* canonical of addoid here will be ignored, so we reclaim distribution lemmas *)
(* Canonical  muld_monoid := Monoid.Law (@muldA _ H) (@mulIId _ H) (@muldII _ H). *)
HB.instance Definition _ := Monoid.isMulLaw.Build 
  'D[H] 0 (@muld _ H) (@mul0d _ H) (@muld0 _ H).
Definition muld_addoid : @Monoid.add_law 'D[H] 0 (@muld _ H) := HB.pack +%R
  (Monoid.isAddLaw.Build 'D[H] (@muld _ H) +%R (@muldDl _ H) (@muldDr _ H)).

HB.instance Definition _ := Monoid.isMulLaw.Build 
  'D[H] 0 (@tend _ H) (@ten0d _ H) (@tend0 _ H).
HB.instance Definition _ := Monoid.isComLaw.Build 
  'D[H] :1 (@tend _ H) (@tendA _ H) (@tendC _ H) (@ten1d _ H).
Definition tend_addoid : @Monoid.add_law 'D[H] 0 (@tend _ H) := HB.pack +%R
  (Monoid.isAddLaw.Build 'D[H] (@tend _ H) +%R (@tendDl _ H) (@tendDr _ H)).

HB.instance Definition _ := Monoid.isMulLaw.Build 
  'D[H] 0 (@dotd _ H) (@dot0d _ H) (@dotd0 _ H).
Definition dotd_addoid : @Monoid.add_law 'D[H] 0 (@dotd _ H) := HB.pack +%R
  (Monoid.isAddLaw.Build 'D[H] (@dotd _ H) +%R (@dotdDl _ H) (@dotdDr _ H)).

Lemma tendsumE : (+%R : 'D[H] -> 'D -> 'D) = tend_addoid. by []. Qed.
Lemma muldsumE : (+%R : 'D[H] -> 'D -> 'D) = muld_addoid. by []. Qed.
Lemma dotdsumE : (+%R : 'D[H] -> 'D -> 'D) = dotd_addoid. by []. Qed.

Lemma ketd_sum I (r : seq I) (P : pred I) S (F : I -> 'H[H]_S) :
  \sum_(i <- r | P i) '|F i> = '|\sum_(i <- r | P i) (F i)>.
Proof. by rewrite linear_sum/=. Qed.

Lemma brad_sum I (r : seq I) (P : pred I) S (F : I -> 'H[H]_S) :
  \sum_(i <- r | P i) '<F i| = '<\sum_(i <- r | P i) (F i)|.
Proof. by rewrite linear_sum/=. Qed.

Lemma lind_sum I (r : seq I) (P : pred I) S T (F : I -> 'F[H]_(S,T)) :
  \sum_(i <- r | P i) '[F i] = '[\sum_(i <- r | P i) (F i)].
Proof. by rewrite linear_sum/=. Qed.

(*distribution lemmas *)
Lemma tend_sumlr I J rI rJ (pI : pred I) (pJ : pred J) 
  (F : I -> 'D[H]) (G : J -> 'D) :
  (\sum_(i <- rI | pI i) F i) \⊗ (\sum_(j <- rJ | pJ j) G j)
   = \sum_(i <- rI | pI i) \sum_(j <- rJ | pJ j) (F i \⊗ G j).
Proof. rewrite !tendsumE; apply: big_distrlr. Qed.

Lemma tend_distr_sum_dep (I J : finType) j0 (P : pred I) (Q : I -> pred J) 
  (F : I -> J -> 'D[H]) :
  (\ten_(i | P i) \sum_(j | Q i j) F i j) =
     \sum_(f in pfamily j0 P Q) \ten_(i | P i) F i (f i).
Proof. rewrite tendsumE bigd; apply: big_distr_big_dep. Qed.

Lemma tend_distr_sum (I J : finType) j0 (P : pred I) (Q : pred J) 
  (F : I -> J -> 'D[H]) :
  (\ten_(i | P i) \sum_(j | Q j) F i j) =
     \sum_(f in pffun_on j0 P Q) \ten_(i | P i) F i (f i).
Proof. by rewrite tendsumE bigd; apply: big_distr_big. Qed.

Lemma tendA_distr_sum_dep (I J : finType) (Q : I -> pred J) 
  (F : I -> J -> 'D[H]) :
  (\ten_i \sum_(j | Q i j) F i j)
    = \sum_(f in family Q) \ten_i F i (f i).
Proof. by rewrite tendsumE bigd; apply: bigA_distr_big_dep. Qed.

Lemma tendA_distr_sum (I J : finType) (Q : pred J) (F : I -> J -> 'D[H]) :
  (\ten_i \sum_(j | Q j) F i j)
    = \sum_(f in ffun_on Q) \ten_i F i (f i).
Proof. exact: tendA_distr_sum_dep. Qed.

Lemma tendA_distr_sumA (I J : finType) (F : I -> J -> 'D[H]) :
  (\ten_(i : I) \sum_(j : J) F i j)
    = \sum_(f : {ffun I -> J}) \ten_i F i (f i).
Proof. by rewrite tendsumE bigd; apply: bigA_distr_bigA. Qed.

(*distribution lemmas *)
Lemma muld_sumlr I J rI rJ (pI : pred I) (pJ : pred J) 
  (F : I -> 'D[H]) (G : J -> 'D) :
  (\sum_(i <- rI | pI i) F i) \o (\sum_(j <- rJ | pJ j) G j)
   = \sum_(i <- rI | pI i) \sum_(j <- rJ | pJ j) (F i \o G j).
Proof. rewrite !muldsumE; apply: big_distrlr. Qed.

Lemma dotd_sumlr I J rI rJ (pI : pred I) (pJ : pred J) 
  (F : I -> 'D[H]) (G : J -> 'D) :
  (\sum_(i <- rI | pI i) F i) \· (\sum_(j <- rJ | pJ j) G j)
   = \sum_(i <- rI | pI i) \sum_(j <- rJ | pJ j) (F i \· G j).
Proof. rewrite !dotdsumE; apply: big_distrlr. Qed.

Lemma dotd_distr_sum_dep (I J : finType) j0 (P : pred I) (Q : I -> pred J) 
  (F : I -> J -> 'D[H]) :
  (\dot_(i | P i) \sum_(j | Q i j) F i j) =
     \sum_(f in pfamily j0 P Q) \dot_(i | P i) F i (f i).
Proof. by rewrite dotdsumE bigd; apply: big_distr_big_dep. Qed.

Lemma dotd_distr_sum (I J : finType) j0 (P : pred I) (Q : pred J) 
  (F : I -> J -> 'D[H]) :
  (\dot_(i | P i) \sum_(j | Q j) F i j) =
     \sum_(f in pffun_on j0 P Q) \dot_(i | P i) F i (f i).
Proof. by rewrite dotdsumE bigd; apply: big_distr_big. Qed.

Lemma dotdA_distr_sum_dep (I J : finType) (Q : I -> pred J) 
  (F : I -> J -> 'D[H]) :
  (\dot_i \sum_(j | Q i j) F i j)
    = \sum_(f in family Q) \dot_i F i (f i).
Proof. by rewrite dotdsumE bigd; apply: bigA_distr_big_dep. Qed.

Lemma dotdA_distr_sum (I J : finType) (Q : pred J) (F : I -> J -> 'D[H]) :
  (\dot_i \sum_(j | Q j) F i j)
    = \sum_(f in ffun_on Q) \dot_i F i (f i).
Proof. exact: dotdA_distr_sum_dep. Qed.

Lemma dotdA_distr_sumA (I J : finType) (F : I -> J -> 'D[H]) :
  (\dot_(i : I) \sum_(j : J) F i j)
    = \sum_(f : {ffun I -> J}) \dot_i F i (f i).
Proof. by rewrite dotdsumE bigd; apply: bigA_distr_bigA. Qed.

(* add dffun for big distr *)
Lemma tendA_distr_big_dffun (I : finType) (J : forall i : I, finType)
  (PJ : forall i : I, pred (J i)) (F : forall i : I, J i -> 'D[H]) :
  (\ten_(i : I) \sum_(j : J i| PJ i j) F i j)
    = \sum_(f : {dffun forall i : I, J i} | 
        family_mem (fun i : I => Mem (PJ i)) f) \ten_i F i (f i).
Proof. rewrite tendsumE bigd; apply: big_distr_big_dffun. Qed.

Lemma tendA_distr_dffun (I : finType) (J : forall i : I, finType)
  (F : forall i : I, J i -> 'D[H]) :
  (\ten_(i : I) \sum_(j : J i) F i j)
    = \sum_(f : {dffun forall i : I, J i}) \ten_i F i (f i).
Proof. rewrite tendsumE bigd; apply: big_distr_dffun. Qed.

Lemma dotdA_distr_big_dffun (I : finType) (J : forall i : I, finType)
  (PJ : forall i : I, pred (J i)) (F : forall i : I, J i -> 'D[H]) :
  (\dot_(i : I) \sum_(j : J i| PJ i j) F i j)
    = \sum_(f : {dffun forall i : I, J i} | 
        family_mem (fun i : I => Mem (PJ i)) f) \dot_i F i (f i).
Proof. rewrite dotdsumE bigd; apply: big_distr_big_dffun. Qed.

Lemma dotdA_distr_dffun (I : finType) (J : forall i : I, finType)
  (F : forall i : I, J i -> 'D[H]) :
  (\dot_(i : I) \sum_(j : J i) F i j)
    = \sum_(f : {dffun forall i : I, J i}) \dot_i F i (f i).
Proof. rewrite dotdsumE bigd; apply: big_distr_dffun. Qed.

End DiracBig.

(* conditioned theory, require extra domain conditions *)
(* This section is used for Canonical Structure of dirac *)
(* for example, we can canonical ketd to ketdirac and wfdirac *)
(* and in the theory, we may set up a lemma (e : wfdirac) : P e *)
(* the for ketd v, we can directly apply the lemma without proving wfd *)

HB.mixin Record isWFDirac {L : finType} {H : L -> chsType} (S T : {set L}) 
  (f : 'D[H]) := { is_wfdirac : '[f S T] = f}.

#[short(type="wfDirac")]
HB.structure Definition WFDirac {L : finType} {H : L -> chsType} (S T : {set L}) := 
  { f of @isWFDirac L H S T f}.

HB.mixin Record WFDirac_isSqr {L : finType} {H : L -> chsType} (S : {set L}) 
  f of @WFDirac L H S S f := { is_sqrdirac : '[f S S] = f}.

#[short(type="sqrDirac")]
HB.structure Definition SqrDirac {L : finType} {H : L -> chsType} (S : {set L}) := 
  { f of @WFDirac L H S S f & WFDirac_isSqr L H S f}.

HB.mixin Record WFDirac_isKet {L : finType} {H : L -> chsType} (S : {set L}) 
  f of @WFDirac L H set0 S f := { is_ketdirac : '[f set0 S] = f}.

#[short(type="ketDirac")]
HB.structure Definition KetDirac {L : finType} {H : L -> chsType} (S : {set L}) := 
  { f of @WFDirac L H set0 S f & WFDirac_isKet L H S f}.

HB.mixin Record WFDirac_isBra {L : finType} {H : L -> chsType} (S : {set L}) 
  f of @WFDirac L H S set0 f := { is_bradirac : '[f S set0] = f}.

#[short(type="braDirac")]
HB.structure Definition BraDirac {L : finType} {H : L -> chsType} (S : {set L}) := 
  { f of @WFDirac L H set0 S f & WFDirac_isBra L H S f}.

HB.factory Record isSqrDirac {L : finType} {H : L -> chsType} (S : {set L}) (f : 'D[H]) := 
  { is_sqrdirac : '[f S S] = f; }.
HB.builders Context L H S f of isSqrDirac L H S f.
  HB.instance Definition _ := isWFDirac.Build L H S S f is_sqrdirac.
  HB.instance Definition _ := WFDirac_isSqr.Build L H S f is_sqrdirac.
HB.end.

HB.factory Record isKetDirac {L : finType} {H : L -> chsType} (S : {set L}) (f : 'D[H]) := 
  { is_ketdirac : '[f set0 S] = f; }.
HB.builders Context L H S f of isKetDirac L H S f.
  HB.instance Definition _ := isWFDirac.Build L H set0 S f is_ketdirac.
  HB.instance Definition _ := WFDirac_isKet.Build L H S f is_ketdirac.
HB.end.

HB.factory Record isBraDirac {L : finType} {H : L -> chsType} (S : {set L}) (f : 'D[H]) := 
  { is_bradirac : '[f S set0] = f; }.
HB.builders Context L H S f of isBraDirac L H S f.
  HB.instance Definition _ := isWFDirac.Build L H S set0 f is_bradirac.
  HB.instance Definition _ := WFDirac_isBra.Build L H S f is_bradirac.
HB.end.

Definition WFDirac_Build {L : finType} {H : L -> chsType} (S T : {set L}) 
  (f : 'D[H]) (Hf : '[f S T] = f) :=
  WFDirac.Pack (WFDirac.Class (isWFDirac.Axioms_ H S T f Hf)).
Definition SqrDirac_Build {L : finType} {H : L -> chsType} (S : {set L}) 
  (f : 'D[H]) (Hf : '[f S S] = f) :=
  SqrDirac.Pack (SqrDirac.Class (WFDirac_isSqr.Axioms_ S f
  (isWFDirac.Axioms_ H S S f Hf) Hf)).
Definition KetDirac_Build {L : finType} {H : L -> chsType} (S : {set L}) 
  (f : 'D[H]) (Hf : '[f set0 S] = f) :=
  KetDirac.Pack (KetDirac.Class (WFDirac_isKet.Axioms_ S f
  (isWFDirac.Axioms_ H set0 S f Hf) Hf)).
Definition BraDirac_Build {L : finType} {H : L -> chsType} (S : {set L}) 
  (f : 'D[H]) (Hf : '[f S set0] = f) :=
  BraDirac.Pack (BraDirac.Class (WFDirac_isBra.Axioms_ S f
  (isWFDirac.Axioms_ H S set0 f Hf) Hf)).
Arguments WFDirac_Build {L H} [S T] f.
Arguments SqrDirac_Build {L H} [S] f.
Arguments KetDirac_Build {L H} [S] f.
Arguments BraDirac_Build {L H} [S] f.

Notation wfdirac_axiom S T f := ('[f%D S T] = f).
Notation sqrdirac_axiom S f := (wfdirac_axiom S S f).
Notation ketdirac_axiom S f := (wfdirac_axiom set0 S f).
Notation bradirac_axiom S f := (wfdirac_axiom S set0 f).

Notation "''D[' H ]_ ( S , T )" := (@wfDirac _ H S T) (only parsing) : dirac_scope.
Notation "''D_' ( S , T )" := (@wfDirac _ _ S T) : dirac_scope.
Notation "''D[' H ]_ ( S )" := (@sqrDirac _ H S) (only parsing) : dirac_scope.
Notation "''D[' H ]_ S" := (@sqrDirac _ H S) (only parsing) : dirac_scope.
Notation "''D_' ( S )" := (@sqrDirac _ _ S) (only parsing) : dirac_scope.
Notation "''D_' S" := (@sqrDirac _ _ S) : dirac_scope.
Notation "''Ket[' H ]_ ( S )" := (@ketDirac _ H S) (only parsing) : dirac_scope.
Notation "''Ket[' H ]_ S" := (@ketDirac _ H S) (only parsing) : dirac_scope.
Notation "''Ket_' ( S )" := (@ketDirac _ _ S) (only parsing) : dirac_scope.
Notation "''Ket_' S" := (@ketDirac _ _ S) : dirac_scope.
Notation "''Bra[' H ]_ ( S )" := (@braDirac _ H S) (only parsing) : dirac_scope.
Notation "''Bra[' H ]_ S" := (@braDirac _ H S) (only parsing) : dirac_scope.
Notation "''Bra_' ( S )" := (@braDirac _ _ S) (only parsing) : dirac_scope.
Notation "''Bra_' S" := (@braDirac _ _ S) : dirac_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use WFDirac.clone instead.")]
Notation "[ 'wfDirac' 'of' e | S , T ]" := (WFDirac.clone _ _ S T e _)
  (at level 0, format "[ 'wfDirac'  'of'  e  |  S  ,  T ]") : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use WFDirac.clone instead.")]
Notation "[ 'wfDirac' 'of' e ]" := (WFDirac.clone _ _ _ _ e _)
  (at level 0, format "[ 'wfDirac'  'of'  e ]") : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use SqrDirac.clone instead.")]
Notation "[ 'sqrDirac' 'of' e | S ]" := (SqrDirac.clone _ _ S e _)
  (at level 0, format "[ 'sqrDirac'  'of'  e  |  S ]") : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use SqrDirac.clone instead.")]
Notation "[ 'sqrDirac' 'of' e ]" := (SqrDirac.clone _ _ _ e _)
  (at level 0, format "[ 'sqrDirac'  'of'  e ]") : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use KetDirac.clone instead.")]
Notation "[ 'ketDirac' 'of' e | S ]" := (KetDirac.clone _ _ S e _)
  (at level 0, format "[ 'ketDirac'  'of'  e  |  S ]") : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use KetDirac.clone instead.")]
Notation "[ 'ketDirac' 'of' e ]" := (KetDirac.clone _ _ _ e _)
  (at level 0, format "[ 'ketDirac'  'of'  e ]") : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use BraDirac.clone instead.")]
Notation "[ 'braDirac' 'of' e | S ]" := (BraDirac.clone _ _ S e _)
  (at level 0, format "[ 'braDirac'  'of'  e  | S ]") : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use BraDirac.clone instead.")]
Notation "[ 'braDirac' 'of' e ]" := (BraDirac.clone _ _ S e _)
  (at level 0, format "[ 'braDirac'  'of'  e ]") : form_scope.

Section WFDiracTheory.
Context (L : finType) (H : L -> chsType).

Lemma wfdiracE S T (e : 'D[H]_(S,T)) : e = '[ e S T] :> 'D.
Proof. by rewrite is_wfdirac. Qed.
Lemma sqrdiracE S (e : 'D[H]_S) : e = '[ e S S] :> 'D.
Proof. by rewrite is_sqrdirac. Qed.
Lemma ketdiracE S (e : 'Ket[H]_S) : e = '| d2v S e > :> 'D.
Proof. by rewrite d2v.unlock ketd.unlock f2vK is_ketdirac. Qed.
Lemma bradiracE S (e : 'Bra[H]_S) : e = '< d2dv S e | :> 'D.
Proof. by rewrite d2dv.unlock brad.unlock df2vK is_bradirac. Qed.

Lemma d2fK {S T} {e : 'D[H]_(S,T)} : '[ d2f S T e] = e.
Proof. by rewrite d2f.unlock is_wfdirac. Qed.
Lemma d2vK {S} {e : 'Ket[H]_S} : '|d2v S e> = e.
Proof. by rewrite -ketdiracE. Qed.
Lemma d2dvK {S} {e : 'Bra[H]_S} : '<d2dv S e| = e.
Proof. by rewrite -bradiracE. Qed.

(* Lemma wfdP S T (e : 'D[H]_(S,T)) : wfd S T e. Proof. by case: e. Qed.
Lemma sqrdP S (e : 'D[H]_S) : sqrd S e. Proof. by case: e. Qed.
Lemma ketP S (e : 'Ket[H]_S) : ketd S e. Proof. by case: e. Qed.
Lemma braP S (e : 'Bra[H]_S) : brad S e. Proof. by case: e. Qed. *)

Lemma wfdP_eq S T S' T' (e : 'D[H]_(S,T)) : 
  S = S' -> T = T' -> '[e S' T'] = e.
Proof. by move=><-<-; rewrite is_wfdirac. Qed.
Lemma sqrdP_eq S S' (e : 'D[H]_S) : S = S' -> '[e S' S'] = e.
Proof. by move=><-; rewrite is_sqrdirac. Qed.
Lemma ketP_eq S S' (e : 'Ket[H]_S) : S = S' -> '|d2v S' e> = e.
Proof. by move=><-; rewrite -ketdiracE. Qed.
Lemma braP_eq S S' (e : 'Bra[H]_S) : S = S' -> '<d2dv S' e| = e.
Proof. by move=><-; rewrite -bradiracE. Qed.

Lemma WFDirac_BuildE S T (e : 'D[H]) (P : '[e S T] = e) : e = WFDirac_Build e P.
Proof. by []. Qed.
Lemma SqrDirac_BuildE S (e : 'D[H]) (P : '[e S S] = e) : e = SqrDirac_Build e P.
Proof. by []. Qed.
Lemma KetDirac_BuildE S (e : 'D[H]) (P : '[e set0 S] = e) : e = KetDirac_Build e P.
Proof. by []. Qed.
Lemma BraDirac_BuildE S (e : 'D[H]) (P : '[e S set0] = e) : e = BraDirac_Build e P.
Proof. by []. Qed.

Lemma wfdirac_eqP S T S' T' (e1 : 'D[H]_(S,T)) (e2 : 'D_(S',T')) :
  (e1 : 'D) = e2 -> ((S == S') && (T == T')) || ((e1 : 'D) == 0).
Proof.
move=>P; case: eqP; case: eqP=>//= /eqP P1 /eqP P2.
all:apply/eqP/diracP=>i j; rewrite (wfdiracE) lind.unlock !diracE; case: eqP=>//; 
  case: eqP=>// P3 P4; rewrite P (wfdiracE).
1,3: by rewrite lind_eq0r// linear0.
by rewrite lind_eq0l// linear0.
Qed.

Lemma sqrdirac_eqP S T (e1 : 'D[H]_S) (e2 : 'D_T) :
  (e1 : 'D) = e2 -> (S == T) || ((e1 : 'D) == 0).
Proof. by move/wfdirac_eqP=>/orP[/andP[->]//|->]; rewrite orbT. Qed.

Lemma ketdirac_eqP S T (e1 : 'Ket[H]_S) (e2 : 'Ket_T) :
  (e1 : 'D) = e2 -> (S == T) || ((e1 : 'D) == 0).
Proof. by move/wfdirac_eqP=>/orP[/andP[_ ->]//|->]; rewrite orbT. Qed.

Lemma bradirac_eqP S T (e1 : 'Bra[H]_S) (e2 : 'Bra_T) :
  (e1 : 'D) = e2 -> (S == T) || ((e1 : 'D) == 0).
Proof. by move/wfdirac_eqP=>/orP[/andP[->]//|->]; rewrite orbT. Qed.

Lemma wfdiracP S T (e1 e2 : 'D_(S,T)) : (e1 : 'D[H]) = e2 <-> e1 = e2.
Proof.
split=>[|->//]; destruct e1 as [e1 [[wf1]]]; destruct e2 as [e2 [[wf2]]] =>/= P.
by case: e2 / P wf2=> wf2; rewrite (eq_irrelevance wf1 wf2).
Qed.

Lemma sqrdiracP S (e1 e2 : 'D_S) : (e1 : 'D[H]) = e2 <-> e1 = e2.
Proof.
split=>[|->//]; destruct e1 as [e1 [[wf1][s1]]]; destruct e2 as [e2 [[wf2][s2]]] =>/= P.
by case: e2 / P wf2 s2=>wf2 s2; rewrite (Prop_irrelevance wf1 wf2) (Prop_irrelevance s1 s2).
Qed.

Lemma ketdiracP S (e1 e2 : 'Ket_S) : (e1 : 'D[H]) = e2 <-> e1 = e2.
Proof.
split=>[|->//]; destruct e1 as [e1 [[wf1][s1]]]; destruct e2 as [e2 [[wf2][s2]]] =>/= P.
by case: e2 / P wf2 s2=>wf2 s2; rewrite (Prop_irrelevance wf1 wf2) (Prop_irrelevance s1 s2).
Qed.

Lemma bradiracP S (e1 e2 : 'Bra_S) : (e1 : 'D[H]) = e2 <-> e1 = e2.
Proof.
split=>[|->//]; destruct e1 as [e1 [[wf1][s1]]]; destruct e2 as [e2 [[wf2][s2]]] =>/= P.
by case: e2 / P wf2 s2=>wf2 s2; rewrite (Prop_irrelevance wf1 wf2) (Prop_irrelevance s1 s2).
Qed.

Lemma zerod_wf S T : wfdirac_axiom S T (0 : 'D[H]).
Proof.
apply/diracP=>i j; rewrite lind.unlock !diracE; 
by (do 2 case: eqP=>//?); rewrite linear0.
Qed.
Canonical zero_wfdirac S T := WFDirac_Build 0 (@zerod_wf S T).
Canonical zero_sqrdirac S  := SqrDirac_Build 0 (@zerod_wf S S).
Canonical zero_ketdirac S  := KetDirac_Build 0 (@zerod_wf set0 S).
Canonical zero_bradirac S  := BraDirac_Build 0 (@zerod_wf S set0).

Lemma numd_wf c : wfdirac_axiom set0 set0 (c%:D : 'D[H]).
Proof. by rewrite numd_lin lind_id. Qed.
Canonical numd_wfdirac c  := WFDirac_Build c%:D (@numd_wf c).
Canonical numd_sqrdirac c := SqrDirac_Build c%:D (@numd_wf c).
Canonical numd_ketdirac c := KetDirac_Build c%:D (@numd_wf c).
Canonical numd_bradirac c := BraDirac_Build c%:D (@numd_wf c).

Lemma ketd_wf S (v : 'H[H]_S) : wfdirac_axiom set0 S '|v>.
Proof. by rewrite ketd_lin lind_id. Qed.
Canonical ketd_wfdirac S (v : 'H_S)   := WFDirac_Build '|v> (ketd_wf v).
Canonical ketd_sqrdirac (v : 'H_set0) := SqrDirac_Build '|v> (ketd_wf v).
Canonical ketd_ketdirac S (v : 'H_S)  := KetDirac_Build '|v> (ketd_wf v).
Canonical ketd_bradirac (v : 'H_set0) := BraDirac_Build '|v> (ketd_wf v).

Lemma brad_wf S (v : 'H[H]_S) : wfdirac_axiom S set0 '<v|.
Proof. by rewrite brad_lin lind_id. Qed.
Canonical brad_wfdirac S (v : 'H_S)   := WFDirac_Build ('<v|) (brad_wf v).
Canonical brad_sqrdirac (v : 'H_set0) := SqrDirac_Build ('<v|) (brad_wf v).
Canonical brad_ketdirac (v : 'H_set0) := KetDirac_Build ('<v|) (brad_wf v).
Canonical brad_bradirac S (v : 'H_S)  := BraDirac_Build ('<v|) (brad_wf v).

Lemma lind_wf S T (f : 'F[H]_(S,T)) : wfdirac_axiom S T '[ f ].
Proof. by rewrite lind_id. Qed.
Canonical lind_wfdirac S T (f : 'F_(S,T))  := WFDirac_Build '[f] (lind_wf f).
Canonical lind_sqrdirac S (f : 'F_S) := SqrDirac_Build '[f] (lind_wf f).
Canonical lind_ketdirac S (f : 'F_(set0,S)) := KetDirac_Build '[f] (lind_wf f).
Canonical lind_bradirac S (f : 'F_(S,set0)) := BraDirac_Build '[f] (lind_wf f).

Lemma addd_wf S T (e1 e2 : 'D[H]_(S,T)) : wfdirac_axiom S T ((e1 : 'D) + e2).
Proof. by rewrite wfdiracE (wfdiracE e2) addd_correct lind_id. Qed.
Canonical addd_wfdirac S T (e1 e2 : 'D_(S,T)) := 
  WFDirac_Build ((e1 : 'D) + e2) (@addd_wf S T e1 e2).
Canonical addd_sqrdirac S (e1 e2 : 'D_S) := 
  SqrDirac_Build ((e1 : 'D) + e2) (addd_wf e1 e2).
Canonical addd_ketdirac S (e1 e2 : 'Ket_S) := 
  KetDirac_Build ((e1 : 'D) + e2) (addd_wf e1 e2).
Canonical addd_bradirac S (e1 e2 : 'Bra_S) := 
  BraDirac_Build ((e1 : 'D) + e2) (addd_wf e1 e2).

Lemma oppd_wf S T (e : 'D[H]_(S,T)) : wfdirac_axiom S T (- (e : 'D)).
Proof. by rewrite wfdiracE oppd_correct lind_id. Qed.
Canonical oppd_wfdirac S T (e : 'D_(S,T))  := WFDirac_Build (- (e : 'D)) (@oppd_wf S T e).
Canonical oppd_sqrdirac S (e : 'D_S) := SqrDirac_Build (- (e : 'D)) (oppd_wf e).
Canonical oppd_ketdirac S (e : 'Ket_S) := KetDirac_Build (- (e : 'D)) (oppd_wf e).
Canonical oppd_bradirac S (e : 'Bra_S) := BraDirac_Build (- (e : 'D)) (oppd_wf e).

Lemma scaled_wf c S T (e : 'D[H]_(S,T)) : wfdirac_axiom S T (c *: (e : 'D)).
Proof. by rewrite wfdiracE scaled_correct lind_id. Qed.
Canonical scaled_wfdirac c S T (e : 'D_(S,T))  := WFDirac_Build (c *: (e : 'D)) (@scaled_wf c S T e).
Canonical scaled_sqrdirac c S (e : 'D_S) := SqrDirac_Build (c *: (e : 'D)) (scaled_wf c e).
Canonical scaled_ketdirac c S (e : 'Ket_S) := KetDirac_Build (c *: (e : 'D)) (scaled_wf c e).
Canonical scaled_bradirac c S (e : 'Bra_S) := BraDirac_Build (c *: (e : 'D)) (scaled_wf c e).

Lemma conjd_wf S T (e : 'D[H]_(S,T)) : wfdirac_axiom S T e^C.
Proof. by rewrite wfdiracE conjd_correct lind_id -conjd_correct. Qed.
Canonical conjd_wfdirac S T (e : 'D_(S,T)) := WFDirac_Build e^C (conjd_wf e).
Canonical conjd_sqrdirac S (e : 'D_S) := SqrDirac_Build e^C (conjd_wf e).
Canonical conjd_ketdirac S (e : 'Ket_S) := KetDirac_Build e^C (conjd_wf e).
Canonical conjd_bradirac S (e : 'Bra_S)  := BraDirac_Build e^C (conjd_wf e).

Lemma adjd_wf S T (e : 'D[H]_(S,T)) : wfdirac_axiom T S e^A.
Proof. by rewrite wfdiracE adjd_correct lind_id -adjd_correct. Qed.
Canonical adjd_wfdirac S T (e : 'D_(S,T)) := WFDirac_Build e^A (adjd_wf e).
Canonical adjd_sqrdirac S (e : 'D_S) := SqrDirac_Build e^A (adjd_wf e).
Canonical adjd_ketdirac S (e : 'Bra_S) := KetDirac_Build e^A (adjd_wf e).
Canonical adjd_bradirac S (e : 'Ket_S)  := BraDirac_Build e^A (adjd_wf e).

Lemma trd_wf S T (e : 'D[H]_(S,T)) : wfdirac_axiom T S e^T.
Proof. by rewrite wfdiracE trd_correct lind_id -trd_correct. Qed.
Canonical trd_wfdirac S T (e : 'D_(S,T)) := WFDirac_Build e^T (trd_wf e).
Canonical trd_sqrdirac S (e : 'D_S) := SqrDirac_Build e^T (trd_wf e).
Canonical trd_ketdirac S (e : 'Bra_S) := KetDirac_Build e^T (trd_wf e).
Canonical trd_bradirac S (e : 'Ket_S)  := BraDirac_Build e^T (trd_wf e).

Lemma muld_wf S T W (e1 : 'D[H]_(S,T)) (e2 : 'D_(W,S)) : 
  wfdirac_axiom W T (e1 \o e2).
Proof. by rewrite wfdiracE (wfdiracE e2) muld_correct lind_id. Qed.
Canonical muld_wfdirac S T W (e1 : 'D_(S,T)) (e2 : 'D_(W,S)) := 
  WFDirac_Build (e1 \o e2) (muld_wf e1 e2).
Canonical muld_sqrdirac S T (e1 : 'D[H]_(S,T)) (e2 : 'D_(T,S)) := 
  SqrDirac_Build (e1 \o e2) (muld_wf e1 e2).
Canonical muld_ketdirac S T (e1 : 'D_(S,T)) (e2 : 'Ket_S) := 
  KetDirac_Build (e1 \o e2) (muld_wf e1 e2).
Canonical muld_bradirac S T (e1 : 'Bra_S) (e2 : 'D_(T,S)) := 
  BraDirac_Build (e1 \o e2) (muld_wf e1 e2).

Lemma tend_wf S T S' T' (e1 : 'D[H]_(S,T)) (e2 : 'D_(S',T')) : 
  wfdirac_axiom (S :|: S') (T :|: T') (e1 \⊗ e2).
Proof. by rewrite wfdiracE (wfdiracE e2) tend_correct lind_id. Qed.
Canonical tend_wfdirac S T S' T' (e1 : 'D_(S,T)) (e2 : 'D_(S',T')) := 
  WFDirac_Build (e1 \⊗ e2) (tend_wf e1 e2).
Canonical tend_sqrdirac S S' (e1 : 'D_S) (e2 : 'D_S') := 
  SqrDirac_Build (e1 \⊗ e2) (tend_wf e1 e2).
Lemma tend_wf_ket S S' (e1 : 'Ket[H]_S) (e2 : 'Ket_S') :
  ketdirac_axiom (S :|: S') (e1 \⊗ e2).
Proof. by rewrite [RHS]wfdiracE/= setU0. Qed.
Lemma tend_wf_bra S S' (e1 : 'Bra[H]_S) (e2 : 'Bra_S') : 
  bradirac_axiom (S :|: S') (e1 \⊗ e2).
Proof. by rewrite [RHS]wfdiracE/= setU0. Qed.
Canonical tend_ketdirac S S' (e1 : 'Ket_S) (e2 : 'Ket_S') :=
  KetDirac_Build (e1 \⊗ e2) (tend_wf_ket e1 e2).
Canonical tend_bradirac S S' (e1 : 'Bra_S) (e2 : 'Bra_S') :=
  BraDirac_Build (e1 \⊗ e2) (tend_wf_bra e1 e2).

Lemma dotd_wf S T S' T' (e1 : 'D[H]_(S,T)) (e2 : 'D_(S',T')) :
  wfdirac_axiom (S' :|: S :\: T') (T :|: T' :\: S) (e1 \· e2).
Proof. by rewrite wfdiracE (wfdiracE e2) dotd_correct lind_id. Qed.
Canonical dotd_wfdirac S T S' T' (e1 : 'D_(S,T)) (e2 : 'D_(S',T')) := 
  WFDirac_Build (e1 \· e2) (dotd_wf e1 e2).
Lemma dotd_wf_sqr S S' (e1 : 'D[H]_S) (e2 : 'D_S') : 
  wfdirac_axiom (S :|: S') (S :|: S') (e1 \· e2).
Proof. by rewrite [RHS]wfdiracE/= setUDV setUD. Qed.
Canonical dotd_sqrdirac S S' (e1 : 'D_S) (e2 : 'D_S') := 
  SqrDirac_Build (e1 \· e2) (dotd_wf_sqr e1 e2).
Lemma dotd_wf_ket S S' (e1 : 'Ket[H]_S) (e2 : 'Ket_S') : 
  ketdirac_axiom (S :|: S') (e1 \· e2).
Proof. by rewrite [RHS]wfdiracE/= set0D setU0 setD0. Qed.
Lemma dotd_wf_bra S S' (e1 : 'Bra[H]_S) (e2 : 'Bra_S') : 
  bradirac_axiom (S :|: S') (e1 \· e2).
Proof. by rewrite [RHS]wfdiracE/= setD0 set0D setU0 setUC. Qed.
Canonical dotd_ketdirac S S' (e1 : 'Ket_S) (e2 : 'Ket_S') := 
  KetDirac_Build (e1 \· e2) (dotd_wf_ket e1 e2).
Canonical dotd_bradirac S S' (e1 : 'Bra_S) (e2 : 'Bra_S') := 
  BraDirac_Build (e1 \· e2) (dotd_wf_bra e1 e2).

Lemma tends_wf I (r : seq I) (P : pred I) (df cdf : I -> {set L})
  (F : forall i : I, 'D[H]_(df i, cdf i)) : 
  wfdirac_axiom (\bigcup_(i <- r | P i) df i) 
    (\bigcup_(i <- r | P i) cdf i) (\ten_(i <- r | P i) F i).
Proof.
rewrite !bigd; elim: r=>[|x r P1]; first by rewrite !big_nil is_wfdirac.
by rewrite !big_cons; case: (P x)=>//; rewrite (WFDirac_BuildE P1) is_wfdirac.
Qed.
Canonical tends_wfdirac I (r : seq I) (P : pred I) (df cdf : I -> {set L}) 
  (F : forall i : I, 'D[H]_(df i, cdf i)) := 
    WFDirac_Build (\ten_(i <- r | P i) F i) (tends_wf r P F).
Canonical tends_sqrdirac I (r : seq I) (P : pred I) (df : I -> {set L})
  (F : forall i : I, 'D[H]_(df i)) := 
    SqrDirac_Build (\ten_(i <- r | P i) F i) (tends_wf r P F).

Lemma tends_wf_ket I (r : seq I) (P : pred I) (df : I -> {set L})
  (F : forall i : I, 'Ket[H]_(df i)) : 
  ketdirac_axiom (\bigcup_(i <- r | P i) df i) (\ten_(i <- r | P i) F i).
Proof. 
have {1 3}->: (set0 : {set L}) = \bigcup_(i <- r | P i) set0 by rewrite big1. 
apply/tends_wf. 
Qed.
Canonical tends_ketdirac I (r : seq I) (P : pred I) (df : I -> {set L})
  (F : forall i : I, 'Ket[H]_(df i)) := 
    KetDirac_Build (\ten_(i <- r | P i) F i) (tends_wf_ket r P F).

Lemma tends_wf_bra I (r : seq I) (P : pred I) (df : I -> {set L})
  (F : forall i : I, 'Bra[H]_(df i)) : 
  bradirac_axiom (\bigcup_(i <- r | P i) df i) (\ten_(i <- r | P i) F i).
Proof. 
have {2 4}->: (set0 : {set L}) = \bigcup_(i <- r | P i) set0 by rewrite big1.
apply/tends_wf.
Qed.
Canonical tends_bradirac I (r : seq I) (P : pred I) (df : I -> {set L})
  (F : forall i : I, 'Bra[H]_(df i)) := 
    BraDirac_Build (\ten_(i <- r | P i) F i) (tends_wf_bra r P F).

(* generally, its better to use lfun for add after calculations *)
Lemma sumd_wf I (r : seq I) (P : pred I) S T (F : I -> 'D[H]_(S,T)) : 
  wfdirac_axiom S T (\sum_(i <- r | P i) (F i : 'D)).
Proof.
elim: r=>[|x r P1]; first by rewrite !big_nil is_wfdirac.
by rewrite !big_cons; case: (P x)=>//; rewrite (WFDirac_BuildE P1) is_wfdirac.
Qed.
Canonical sumd_wfdirac I (r : seq I) (P : pred I) S T (F : I -> 'D[H]_(S,T)) :=
  WFDirac_Build (\sum_(i <- r | P i) (F i : 'D)) (sumd_wf r P F).
Canonical sumd_sqrdirac I (r : seq I) (P : pred I) S (F : I -> 'D[H]_S) :=
  SqrDirac_Build (\sum_(i <- r | P i) (F i : 'D)) (sumd_wf r P F).
Canonical sumd_ketdirac I (r : seq I) (P : pred I) S (F : I -> 'Ket[H]_S) :=
  KetDirac_Build (\sum_(i <- r | P i) (F i : 'D)) (sumd_wf r P F).
Canonical sumd_bradirac I (r : seq I) (P : pred I) S (F : I -> 'Bra[H]_S) :=
  BraDirac_Build (\sum_(i <- r | P i) (F i : 'D)) (sumd_wf r P F).

(* big dot only canonical when: all square, all ket and all bra *)
Lemma dotds_wf_sqr I (r : seq I) (P : pred I) (df : I -> {set L})
 (F : forall i, 'D[H]_(df i)) : 
  sqrdirac_axiom (\bigcup_(i <- r | P i) df i) (\dot_(i <- r | P i) (F i : 'D)).
Proof.
rewrite !bigd; elim: r=>[|x r P1]; first by rewrite !big_nil is_sqrdirac.
by rewrite !big_cons; case: (P x)=>//; rewrite (SqrDirac_BuildE P1) is_sqrdirac.
Qed.
Canonical dotds_sqrdirac I (r : seq I) (P : pred I) (df : I -> {set L})
  (F : forall i, 'D[H]_(df i)) 
 := SqrDirac_Build (\dot_(i <- r | P i) (F i : 'D)) (dotds_wf_sqr r P F).

Lemma dotds_wf_ket I (r : seq I) (P : pred I) (df : I -> {set L})
  (F : forall i, 'Ket[H]_(df i)) : 
  ketdirac_axiom (\bigcup_(i <- r | P i) df i) (\dot_(i <- r | P i) (F i : 'D)).
Proof.
rewrite !bigd; elim: r=>[|x r P1]; first by rewrite !big_nil is_ketdirac.
by rewrite !big_cons; case: (P x)=>//; rewrite (KetDirac_BuildE P1) is_ketdirac.
Qed.
Canonical dotds_ketdirac I (r : seq I) (P : pred I) (df : I -> {set L})
  (F : forall i, 'Ket[H]_(df i)) 
  := KetDirac_Build (\dot_(i <- r | P i) (F i : 'D)) (dotds_wf_ket r P F).

Lemma dotds_wf_bra I (r : seq I) (P : pred I) (df : I -> {set L})
  (F : forall i, 'Bra[H]_(df i)) : 
  bradirac_axiom (\bigcup_(i <- r | P i) df i) (\dot_(i <- r | P i) (F i : 'D)).
Proof.
rewrite !bigd; elim: r=>[|x r P1]; first by rewrite !big_nil is_bradirac.
by rewrite !big_cons; case: (P x)=>//; rewrite (BraDirac_BuildE P1) is_bradirac.
Qed.
Canonical dotds_bradirac I (r : seq I) (P : pred I) (df : I -> {set L})
  (F : forall i, 'Bra[H]_(df i))
 := BraDirac_Build (\dot_(i <- r | P i) (F i : 'D)) (dotds_wf_bra r P F).

(* extra conditions, used to add user-defined structures *)

Lemma sqr_linP S S' (P : 'F[H]_S) : sqrdirac_axiom S' (lind P) <-> ((S == S') || (P == 0)).
Proof.
split. case: eqP=>//; case: eqP=>// H1 /eqP H2 H3.
exfalso. apply H1. move: H3; rewrite lind_eq0l 1?eq_sym// =>/diracP/(_ S S).
by rewrite lind_id linear0 diracE.
by move=>/orP[/eqP<-|/eqP->]; rewrite ?linear0 is_sqrdirac.
Qed.

(* form is frequently used, define dform to provide canonical structure *)
Definition dform (e1 e2 : 'D[H]) := e1^A \· e2 \· e1.
Lemma dformE (e1 e2 : 'D[H]) : dform e1 e2 = e1^A \· e2 \· e1. Proof. by []. Qed.
Lemma dform_sqr S T W (e1 : 'D[H]_(S,T)) (e2 : 'D_W) :
  sqrdirac_axiom (S :|: W :\: T) (dform e1 e2).
Proof.
rewrite /dform wfdiracE sqrdiracE adjd_lin !dotd_correct wfdP_eq//; setdec.
Qed.
Canonical dform_wfdirac S T W (e1 : 'D[H]_(S,T)) (e2 : 'D_W) := 
  WFDirac_Build (dform e1 e2) (dform_sqr e1 e2).
Canonical dform_sqrdirac S T W (e1 : 'D[H]_(S,T)) (e2 : 'D_W) := 
  SqrDirac_Build (dform e1 e2) (dform_sqr e1 e2).

Lemma dform_is_linear e1 : linear (@dform e1).
Proof. by move=>a x y; rewrite /dform linearPr/= linearPl/=. Qed.
HB.instance Definition _ e1 := GRing.isLinear.Build 
  C 'D[H] 'D[H] *:%R (dform e1) (dform_is_linear e1).

Lemma dformEV (e1 e2 : 'D[H]) : dform e1^A e2 = e1 \· e2 \· e1^A.
Proof. by rewrite dformE adjdK. Qed.

End WFDiracTheory.

Section ExtraDiracTheory.
Context {L : finType} (H : L -> chsType).
Implicit Type (S T W : {set L}).

Lemma tendfC S T S' T' (f: 'F[H]_(S,T)) (g: 'F_(S',T')) : 
  '[f \⊗ g] = '[g \⊗ f].
Proof. by rewrite -tend_correct tendC tend_correct. Qed.

Lemma tendfA S1 T1 S2 T2 S3 T3 (f: 'F[H]_(S1,T1)) (g: 'F_(S2,T2))
  (h: 'F[H]_(S3,T3)) : 
  '[ f \⊗ (g \⊗ h) ] = '[ (f \⊗ g) \⊗ h ].
Proof. by rewrite -!tend_correct tendA. Qed.

Lemma tendf1 S T (f: 'F[H]_(S,T))  : 
  '[ f \⊗ (\1 : 'F_set0) ] = '[f].
Proof. by rewrite -tend_correct lindI1 tend1. Qed.

Lemma tend1f S T (f: 'F[H]_(S,T))  : 
  '[ (\1 : 'F_set0) \⊗ f ] = '[f].
Proof. by rewrite tendfC tendf1. Qed.

Lemma dotdfA S1 T1 S2 T2 S3 T3 (f: 'F[H]_(S1,T1)) (g: 'F_(S2,T2))
  (h: 'F_(S3,T3)) : 
  [disjoint S2 & S1 :\: T2] -> [disjoint T2 & T3 :\: S2] ->
  '[ f \· (g \· h) ] = '[ f \· g \· h ].
Proof. by move=>P1 P2; to_Fnd; rewrite dotFA_cond. Qed.  

Lemma dotdA_cond S1 T1 S2 T2 S3 T3 (e1: 'D[H]_(S1,T1)) (e2: 'D_(S2,T2))
  (e3: 'D_(S3,T3)) :
  [disjoint S2 & S1 :\: T2] -> [disjoint T2 & T3 :\: S2] ->
  e1 \· (e2 \· e3) = e1 \· e2 \· e3.
Proof. 
by move=>P1 P2; rewrite wfdiracE (wfdiracE e2) (wfdiracE e3) !dotd_correct dotdfA.
Qed.

Lemma dotdA S1 T1 S2 S3 T3 (e1: 'D[H]_(S1,T1)) (e2: 'D_S2)
  (e3: 'D_(S3,T3)) :
  e1 \· (e2 \· e3) = e1 \· e2 \· e3.
Proof. by rewrite dotdA_cond// disjointXD. Qed.

Lemma dform_comp S T S' W (e1 : 'D[H]_(S,T)) (e2 : 'D_S') (e3 : 'D_W) :
  dform e1 (dform e2 e3) = dform (e2 \· e1) e3.
Proof. by rewrite !dformE adjdG !dotdA_cond//; setdec. Qed.

Lemma dform_compv S S' W W' (e1 : 'Bra[H]_S) (e2 : 'Ket_S') (e3 : 'D_(W,W')) :
  dform e1 (dform e2 e3) = dform (e2 \· e1) e3.
Proof. by rewrite !dformE adjdG !dotdA_cond//; setdec. Qed.

Lemma dotdf_ten S1 T1 S2 T2 (f: 'F[H]_(S1,T1)) (g: 'F_(S2,T2)) :
  [disjoint S1 & T2] -> 
  '[ f \· g ] = '[ f \⊗ g ].
Proof. by move=>P3; to_Fnd; rewrite/= dotFT. Qed.

Lemma dotd_ten S1 T1 S2 T2 (e1: 'D[H]_(S1,T1)) (e2: 'D_(S2,T2)) :
  [disjoint S1 & T2] -> 
  e1 \· e2 = e1 \⊗ e2.
Proof. 
by move=>P1; rewrite wfdiracE (wfdiracE e2) !dotd_correct tend_correct dotdf_ten.
Qed.

Lemma dotdfC S T S' T' (f: 'F[H]_(S,T)) (g: 'F_(S',T')) : 
  [disjoint S & T'] -> [disjoint T & S'] ->
  '[ f \· g ] = '[ g \· f ].
Proof. by move=>P1 P2; to_Fnd; rewrite dotFC. Qed.

Lemma dotdC S T S' T' (e1: 'D[H]_(S,T)) (e2: 'D_(S',T')) :
  [disjoint S & T'] -> [disjoint T & S'] ->
  e1 \· e2 = e2 \· e1.
Proof. 
by move=>P1 P2; rewrite wfdiracE (wfdiracE e2) !dotd_correct dotdfC.
Qed.

Lemma dotdf1 S T (f: 'F[H]_(S,T))  : 
  '[ f \· (\1 : 'F_set0) ] = '[f].
Proof. by to_Fnd; rewrite dotF1. Qed.

Lemma dotd1f S T (f: 'F[H]_(S,T))  : 
  '[ (\1 : 'F_set0) \· f ] = '[f].
Proof. by to_Fnd; rewrite dot1F. Qed.

Lemma dotdf_comp S T W (f: 'F[H]_(S,T)) (g: 'F_(W,S)) :
  '[ f \· g ] = '[ f \o g ].
Proof. by to_Fnd. Qed.

Lemma dotd_mul S T W (e1: 'D[H]_(S,T)) (e2: 'D_(W,S)) :
  e1 \· e2 = e1 \o e2.
Proof. 
by rewrite wfdiracE (wfdiracE e2) !dirac_correct dotdf_comp.
Qed.

Lemma mulId S T (e : 'D[H]_(T,S)) : \1_S \o e = e.
Proof. by rewrite wfdiracE muld_correct comp_lfun1l. Qed.

Lemma muldI S T (e : 'D[H]_(S,T)) : e \o \1_S = e.
Proof. by rewrite wfdiracE muld_correct comp_lfun1r. Qed.

Lemma muld_lin S T W (e1 : 'D[H]_(S,T)) (e2 : 'D_(W,S)) :
  e1 \o e2 = lind (e1 S T \o e2 W S).
Proof. by rewrite {1}wfdiracE {1}(wfdiracE e2) muld_correct. Qed.

Lemma tend_mul S T S' T' W W' (e1: 'D[H]_(S,T)) (e2: 'D_(W,S)) 
  (e3: 'D_(S',T')) (e4: 'D_(W',S')) :
  [disjoint S & S'] ->
  (e1 \⊗ e3) \o (e2 \⊗ e4) = (e1 \o e2) \⊗ (e3 \o e4).
Proof.
by move=>P; rewrite wfdiracE (wfdiracE e2) (wfdiracE e3) (wfdiracE e4) !dirac_correct tenf_comp.
Qed.

Lemma dotIdT S T W (e : 'D[H]_(T,W)) : \1_S \· e =  \1_(S :\: W) \⊗ e.
Proof.
rewrite wfdiracE !dirac_correct; to_Fnd; 
by rewrite dotIF dotFT//= disjointDX.
Qed.

Lemma dotdIT S T W (e : 'D[H]_(T,W)) : e \· \1_S =  \1_(S :\: T) \⊗ e.
Proof.
rewrite tendC wfdiracE !dirac_correct; to_Fnd;
by rewrite dotFI dotFT//= disjointXD.
Qed.

Lemma dotId S T W (e : 'D[H]_(T,W)) : \1_S \· e =  \1_(S :\: W) \· e.
Proof. by rewrite dotIdT dotd_ten// disjointDX. Qed.

Lemma dotdI S T W (e : 'D[H]_(T,W)) : e \· \1_S = e \· \1_(S :\: T).
Proof. by rewrite dotdIT tendC dotd_ten// disjointXD. Qed.

Lemma dotIdid S T W (e : 'D[H]_(T,W)) : S :<=: W -> \1_S \· e = e.
Proof. by rewrite -setD_eq0 dotIdT=>/eqP->; rewrite lindI1 ten1d. Qed.

Lemma dotdIid S T W (e : 'D[H]_(T,W)) : S :<=: T -> e \· \1_S = e.
Proof. by rewrite -setD_eq0 dotdIT=>/eqP->; rewrite lindI1 ten1d. Qed.

Lemma dotd_multen S T S' T' (e1 : 'D[H]_(S,T)) (e2 : 'D_(S',T')) : 
  e1 \· e2 = (e1 \⊗ \1_( T' :\: S )) \o (e2 \⊗ \1_( S :\: T' )).
Proof.
rewrite wfdiracE (wfdiracE e2) !dirac_correct.
by rewrite dot_lfun.unlock -muld_correct lind_cast -!tend_correct/=.
Qed.

Lemma dotd_muldot S T S' T' (e1 : 'D[H]_(S,T)) (e2 : 'D[H]_(S',T')) :
  e1 \· e2 = (e1 \· \1_T') \o (\1_S \· e2).
Proof. by rewrite dotd_multen/= tendC -dotdIT/= tendC -dotIdT. Qed.

Lemma tendII S T : (\1_S : 'D[H]) \⊗ (\1_T) = \1_(S :|: T).
Proof. by rewrite tend_correct tenf11. Qed.

Lemma dotdII S T : (\1_S : 'D[H]) \· (\1_T) = \1_(S :|: T).
Proof. by rewrite dotdI/= dotd_ten ?disjointXD//= tendII setUD. Qed.

Lemma d2cK (e : 'D[H]_(set0,set0)) : (d2c e)%:D = e.
Proof. by rewrite wfdiracE d2c.unlock lind_id numd_lin sf2sK. Qed.

Lemma innerM S (u v : 'H[H]_S) : '<u| \o '|v> = [<u ; v>]%:D.
Proof. by rewrite brad_lin ketd_lin muld_correct comp_dot -numd_lin. Qed.
Lemma innerG S (u v : 'H[H]_S) : '<u| \· '|v> = [<u ; v>]%:D.
Proof. by rewrite dotd_mul/= innerM. Qed.
Lemma outerM S T (u : 'H[H]_S) (v : 'H[H]_T) : '|v> \o '<u| = '[ [> v ; u <] ].
Proof. by rewrite brad_lin ketd_lin muld_correct comp_out. Qed.
Lemma outerG S T (u : 'H[H]_S) (v : 'H[H]_T) : '|v> \· '<u| = '[ [> v ; u <] ].
Proof. by rewrite dotd_mul/= outerM. Qed.
Definition innerE := (innerM, innerG).
Definition outerE := (outerM, outerG).

Definition ketd_conj := (@conjd_ket _ H).
Definition ketd_adj  := (@adjd_ket _ H).
Definition ketd_tr   := (@trd_ket _ H).
Lemma ketdT S T (u: 'H[H]_S) (v: 'H_T) : '|u> \⊗ '|v> = '|u ⊗v v>.
Proof.
rewrite 2!ketd_lin tend_correct /v2f tenf_outp tenv_idx0r -outerM -[RHS]muldI/=.
by f_equal; rewrite brad_cast !numd_simp /sf2s /sv2s lfunE/= dv_dot eqxx conjc1.
Qed.

Definition brad_conj := (@conjd_bra _ H).
Definition brad_adj  := (@adjd_bra _ H).
Definition brad_tr   := (@trd_bra _ H).
Lemma bradT S T (u: 'H[H]_S) (v: 'H_T) : '<u| \⊗ '<v| = '<u ⊗v v|.
Proof. by rewrite -!ketd_adj -adjdT ketdT. Qed.

Definition lind_conj := (@conjd_lin _ H).
Definition lind_adj  := (@adjd_lin _ H).
Definition lind_tr   := (@trd_lin _ H).
Lemma lindM S T W (f : 'F[H]_(S,T)) (g : 'F_(W,S)) : '[f] \o '[g] = '[f \o g].
Proof. by rewrite muld_correct. Qed.

Lemma lindG S T W (f : 'F[H]_(S,T)) (g : 'F_(W,S)) : '[f] \· '[g] = '[f \o g].
Proof. by rewrite dotd_mul/= lindM. Qed.

Lemma lindT S T S' T' (f : 'F[H]_(S,T)) (g : 'F_(S',T')) :
  '[f] \⊗ '[g] = '[f \⊗ g].
Proof. by rewrite tend_correct. Qed.

Lemma lind_ketM S T (f : 'F[H]_(S,T)) (v : 'H_S) : '[f] \o '|v> = '|f v>.
Proof. by rewrite !ketd_lin muld_correct -[(_ \o _)%VF]f2vK v2f_comp. Qed. 

Lemma lind_ketG S T (f : 'F[H]_(S,T)) (v : 'H_S) : '[f] \· '|v> = '|f v>.
Proof. by rewrite dotd_mul/= lind_ketM. Qed.

(* Definition lind_ket := (lind_ketM, lind_ketG). *)

Lemma lind_braM S T (f : 'F[H]_(S,T)) (v : 'H_T) : '<v| \o '[f] = '<f^A v|.
Proof. by rewrite -[_ \o _]adjdK adjdM brad_adj lind_adj lind_ketM ketd_adj. Qed.

Lemma lind_braG S T (f : 'F[H]_(S,T)) (v : 'H_T) : '<v| \· '[f] = '<f^A v|.
Proof. by rewrite dotd_mul/= lind_braM. Qed.

(* Definition lind_bra := (lind_braM, lind_braG). *)

Lemma dotfTl (S1 S2 S3 T1 T2 T3 : {set L}) (f : 'F[H]_(S1,T1)) 
  (g : 'F_(S2,T2)) (h : 'F_(S3,T3)) :
  [disjoint S1 & T3] -> [disjoint T2 & T3] ->
  f \· (g \⊗ h) =c f \· g \⊗ h.
Proof.
move=>P1 P2; rewrite -{2}[h]comp_lfun1l dot_lfun.unlock tenf_comp/=.
move: P1 P2; setdec. to_Fnd; f_equal.
rewrite -tenFA tenF11; f_equal; apply Fnd_eq1.
rewrite setDUl; f_equal; apply/setDidPl; move: P1 P2; setdec.
rewrite tenFC tenFA; f_equal; rewrite tenFC; f_equal; apply Fnd_eq1.
by move: P1=>/setDidPl; rewrite setUC -setDDl=>->.
Qed.

Lemma dotfTr (S1 S2 S3 T1 T2 T3 : {set L}) (f : 'F[H]_(S1,T1)) 
  (g : 'F[H]_(S2,T2)) (h : 'F[H]_(S3,T3)) :
  [disjoint T1 & S3] -> [disjoint S2 & S3] ->
    (g \⊗ h) \· f =c g \· f \⊗ h.
Proof.
move=> P1 P2; rewrite -{2}[h]comp_lfun1r dot_lfun.unlock tenf_comp/=.
move: P1 P2; setdec. to_Fnd; f_equal.
rewrite -!tenFA; f_equal; rewrite tenFC; f_equal; apply Fnd_eq1.
by move: P1=>/setDidPl; rewrite setUC -setDDl=>->.
rewrite -tenFA tenF11; f_equal; apply Fnd_eq1.
rewrite setDUl; f_equal; apply/setDidPl; move: P1 P2; setdec.
Qed.

Lemma dotdTll S1 S2 S3 T1 T2 T3 (e1 : 'D[H]_(S1,T1)) 
  (e2 : 'D_(S2,T2)) (e3 : 'D_(S3,T3)) :
  [disjoint S1 & T3] -> [disjoint T2 & T3] ->
  e1 \· (e2 \⊗ e3) = e1 \· e2 \⊗ e3.
Proof.
move=>P1 P2. rewrite wfdiracE (wfdiracE e2) (wfdiracE e3).
by rewrite !dirac_correct; apply lind_eqFnd; rewrite dotfTl.
Qed.

Lemma dotdTlr S1 S2 S3 T1 T2 T3 (e1 : 'D[H]_(S1,T1)) 
  (e2 : 'D_(S2,T2)) (e3 : 'D_(S3,T3)) : 
  [disjoint S1 & T2] -> [disjoint T3 & T2] ->
    e1 \· (e2 \⊗ e3) = e2 \⊗ (e1 \· e3).
Proof. by move=>P1 P2; rewrite tendC dotdTll 1?tendC. Qed.

Lemma dotdTrl S1 S2 S3 T1 T2 T3 (e1 : 'D[H]_(S1,T1)) 
  (e2 : 'D_(S2,T2)) (e3 : 'D_(S3,T3)) :
  [disjoint T1 & S3] -> [disjoint S2 & S3] ->
  (e2 \⊗ e3) \· e1 = (e2 \· e1) \⊗ e3.
Proof.
move=>P1 P2. rewrite wfdiracE (wfdiracE e1) (wfdiracE e3).
by rewrite !dirac_correct; apply lind_eqFnd; rewrite dotfTr.
Qed.

Lemma dotdTrr S1 S2 S3 T1 T2 T3 (e1 : 'D[H]_(S1,T1)) 
  (e2 : 'D_(S2,T2)) (e3 : 'D_(S3,T3)) :
  [disjoint T1 & S2] -> [disjoint S3 & S2] ->
  (e2 \⊗ e3) \· e1 = e2 \⊗ (e3 \· e1).
Proof. by move=>P1 P2; rewrite tendC dotdTrl 1?tendC. Qed.

Lemma lind_linTll S T S' T' (f : 'F[H]_S) (g : 'F[H]_(T,S)) (e : 'D_(S',T')) : 
  [disjoint S & T'] ->
  '[ f ] \· ('[ g ] \⊗ e) = '[ f \o g ] \⊗ e.
Proof. by move=>P1; rewrite -lindG dotdTll. Qed.

Lemma lind_linTlr S T S' T' (f : 'F[H]_S) (g : 'F[H]_(T,S)) (e : 'D_(S',T')) :
  [disjoint S & T'] ->
  '[ f ] \· (e \⊗ '[ g ]) = e \⊗ '[ f \o g ].
Proof. by move=>P1; rewrite -lindG dotdTlr. Qed.

Lemma lind_linTrl S T S' T' (f : 'F[H]_(S,T)) (g : 'F[H]_S) (e : 'D_(S',T')) : 
  [disjoint S & S'] ->
  ('[ f ] \⊗ e) \· '[ g ] = '[ f \o g ] \⊗ e.
Proof. by move=>P1; rewrite -lindG dotdTrl. Qed.

Lemma lind_linTrr S T S' T' (f : 'F[H]_(S,T)) (g : 'F[H]_S) (e : 'D_(S',T')) : 
  [disjoint S & S'] ->
  (e \⊗ '[ f ]) \· '[ g ] = e \⊗ '[ f \o g ].
Proof. by move=>P1; rewrite -lindG dotdTrr. Qed.

Lemma lind_ketTl S S' T' (f : 'F[H]_S) (v : 'H[H]_S) (e : 'D_(S',T')) : 
  [disjoint S & T'] ->
  '[ f ] \· ('|v> \⊗ e) = '|f v> \⊗ e.
Proof. by move=>P1; rewrite -lind_ketG dotdTll. Qed.

Lemma lind_ketTr S S' T' (f : 'F[H]_S) (v : 'H[H]_S) (e : 'D_(S',T')) : 
  [disjoint S & T'] ->
  '[ f ] \· (e \⊗ '|v>) = e \⊗ '|f v>.
Proof. by move=>P1; rewrite -lind_ketG dotdTlr. Qed.

Lemma lind_braTl S S' T' (f : 'F[H]_S) (v : 'H[H]_S) (e : 'D_(S',T')) : 
  [disjoint S & S'] ->
  ('<v| \⊗ e) \· '[ f ] = '<f^A v| \⊗ e.
Proof. by move=>P1; rewrite -lind_braG dotdTrl. Qed.

Lemma lind_braTr S S' T' (f : 'F[H]_S) (v : 'H[H]_S) (e : 'D_(S',T')) : 
  [disjoint S & S'] ->
  (e \⊗ '<v|) \· '[ f ] = e \⊗ '<f^A v|.
Proof. by move=>P1; rewrite -lind_braG dotdTrr. Qed.

Lemma form_dot_mul S T (e : 'D[H]_(S,T)) : e \· e^A = e \o e^A.
Proof. by rewrite dotd_mul. Qed.

Lemma tends_adj (I : Type) (r : seq I) (P : pred I) (F : I -> 'D[H]) :
  (\ten_(i <- r | P i) F i)^A = \ten_(i <- r | P i) (F i)^A.
Proof.
rewrite !bigd; elim: r=>[|x r IH]; first by rewrite !big_nil adjd1.
by rewrite !big_cons; case: (P x)=>//; rewrite adjdT IH.
Qed.

Lemma tends_tr (I : Type) (r : seq I) (P : pred I) (F : I -> 'D[H]) :
  (\ten_(i <- r | P i) F i)^T = \ten_(i <- r | P i) (F i)^T.
Proof.
rewrite !bigd; elim: r=>[|x r IH]; first by rewrite !big_nil trd1.
by rewrite !big_cons; case: (P x)=>//; rewrite trdT IH.
Qed.

Lemma tends_conj (I : Type) (r : seq I) (P : pred I) (F : I -> 'D[H]) :
(\ten_(i <- r | P i) F i)^C = \ten_(i <- r | P i) (F i)^C.
Proof. by rewrite dC2AT tends_adj tends_tr; under eq_bigr do rewrite -dC2AT. Qed.

Lemma ketBT_adj (I : Type) (r : seq I) (P : pred I) (d : I -> {set L}) 
  (F : forall i, 'H[H]_(d i)) :
  (\ten_(i <- r | P i) '|F i>)^A = \ten_(i <- r | P i) '<F i|.
Proof. by rewrite tends_adj; under eq_bigr do rewrite ketd_adj. Qed.

Lemma ketBT_tr (I : Type) (r : seq I) (P : pred I) (d : I -> {set L}) 
  (F : forall i, 'H[H]_(d i)) :
  (\ten_(i <- r | P i) '|F i>)^T = \ten_(i <- r | P i) '<(F i)^*v|.
Proof. by rewrite tends_tr; under eq_bigr do rewrite ketd_tr. Qed.

Lemma ketBT_conj (I : Type) (r : seq I) (P : pred I) (d : I -> {set L}) 
  (F : forall i, 'H[H]_(d i)) :
(\ten_(i <- r | P i) '|F i>)^C = \ten_(i <- r | P i) '|(F i)^*v>.
Proof. by rewrite tends_conj; under eq_bigr do rewrite ketd_conj. Qed.

Lemma braBT_adj (I : Type) (r : seq I) (P : pred I) (d : I -> {set L}) 
  (F : forall i, 'H[H]_(d i)) :
  (\ten_(i <- r | P i) '<F i|)^A = \ten_(i <- r | P i) '|F i>.
Proof. by rewrite tends_adj; under eq_bigr do rewrite brad_adj. Qed.

Lemma braBT_tr (I : Type) (r : seq I) (P : pred I) (d : I -> {set L}) 
  (F : forall i, 'H[H]_(d i)) :
(\ten_(i <- r | P i) '<F i|)^T = \ten_(i <- r | P i) '|(F i)^*v>.
Proof. by rewrite tends_tr; under eq_bigr do rewrite brad_tr. Qed.

Lemma braBT_conj (I : Type) (r : seq I) (P : pred I) (d : I -> {set L}) 
  (F : forall i, 'H[H]_(d i)) :
  (\ten_(i <- r | P i) '<F i|)^C = \ten_(i <- r | P i) '<(F i)^*v|.
Proof. by rewrite tends_conj; under eq_bigr do rewrite brad_conj. Qed.

Lemma tendsZ (T : Type) (r : seq T) (P : pred T) (fz : T -> C) (e : T -> 'D[H]) :
  \ten_(i <- r | P i) ((fz i) *: (e i)) = 
    \prod_(i <- r | P i) (fz i) *: \ten_(i <- r | P i) (e i).
Proof.
elim/big_rec3: _=>[|i e1 c e2 _]; first by rewrite bigd scale1r.
by rewrite bigd=>->; rewrite tendZl tendZr scalerA.
Qed.

Lemma tendsI F (r : seq F) (P : pred F) (fd : F -> {set L}) :
  \ten_(i <- r | P i) \1_(fd i) = \1_(\bigcup_(i <- r | P i) fd i) :> 'D[H].
Proof.
elim/big_rec2: _=>[|i x y]; first by rewrite bigd numd1I.
by move=>Pi; rewrite bigd=>->; rewrite tendII.
Qed.

Lemma tendsM (I : eqType) (r : seq I) (P : pred I) (d1 d2 d3 : I -> {set L})
  (F : forall i : I, 'D[H]_(d1 i, d2 i)) (G : forall i : I, 'D_(d3 i, d1 i)) :
  (forall i j, P i -> P j -> (i != j) -> [disjoint d1 i & d1 j]) -> 
  uniq r ->
  (\ten_(i <- r | P i) F i) \o \ten_(i <- r | P i) (G i) = 
  (\ten_(i <- r | P i) (F i \o G i)).
Proof.
elim: r=>[_|x r IH]; first by rewrite !big_nil bigd {1}numd1I mulId.
move=>Pij. rewrite cons_uniq=>/andP[Px ur].
rewrite !big_cons; case E: (P x); last by apply IH.
rewrite ?bigdE tend_mul/= ?IH//.
apply/bigcup_disjoint_seqP=>i /andP[ii Pi]; apply Pij=>//.
by move: Px; move=>/memPnC/(_ _ ii).
Qed.

Lemma numdBT (I : eqType) (r : seq I) (P : pred I) (F : I -> C) :
\ten_(i <- r | P i) ((F i)%:D : 'D[H]) = (\prod_(i <- r | P i) (F i))%:D.
Proof.
elim: r=>[|x r IH]; first by rewrite !big_nil bigd.
by rewrite !big_cons; case: (P x)=>[|//]; rewrite bigdE IH numdT; f_equal.
Qed.

Lemma outerMBT (I : Type) (r : seq I) (P : pred I) (Dv Du : I -> {set L}) 
  (Vs : forall i, 'H[H]_(Dv i)) (Us : forall i, 'H[H]_(Du i)) : 
  (\ten_(i <- r | P i) '|Vs i>) \o (\ten_(i <- r | P i) '<Us i|) 
  = \ten_(i <- r | P i) ('|Vs i> \o '<Us i|).
Proof.
elim: r=>[|x r IH]; first by rewrite !big_nil bigd {1}numd1I mulId.
rewrite !big_cons; case E: (P x); last by apply IH.
by rewrite ?bigdE tend_mul ?disjoint0X//= IH.
Qed.

Lemma outerGBT (I : Type) (r : seq I) (P : pred I) (Dv Du : I -> {set L}) 
  (Vs : forall i, 'H[H]_(Dv i)) (Us : forall i, 'H[H]_(Du i)) : 
  (\ten_(i <- r | P i) '|Vs i>) \· (\ten_(i <- r | P i) '<Us i|) 
  = \ten_(i <- r | P i) ('|Vs i> \· '<Us i|).
Proof.
rewrite dotd_mul/= outerMBT//. 
by under eq_bigr do rewrite -dotd_mul.
Qed.

Lemma innerMBT (I : eqType) (r : seq I) (P : pred I) (Ds : I -> {set L}) 
  (Vs Us : forall i, 'H[H]_(Ds i)) : 
    (forall i j, P i -> P j -> (i != j) -> [disjoint Ds i & Ds j]) -> uniq r ->
      (\ten_(i <- r | P i) '<Vs i|) \o (\ten_(i <- r | P i) '|Us i>)
        = (\prod_(i <- r | P i) [<Vs i ; Us i>])%:D.
Proof.
by move=>P1 P2; rewrite tendsM// -numdBT; under eq_bigr do rewrite innerM.
Qed.

Lemma innerGBT (I : eqType) (r : seq I) (P : pred I) (Ds : I -> {set L}) 
  (Vs Us : forall i, 'H[H]_(Ds i)) : 
    (forall i j, P i -> P j -> (i != j) -> [disjoint Ds i & Ds j]) -> uniq r ->
      (\ten_(i <- r | P i) '<Vs i|) \· (\ten_(i <- r | P i) '|Us i>)
        = (\prod_(i <- r | P i) [<Vs i ; Us i>])%:D.
Proof. by rewrite dotd_mul/=; apply innerMBT. Qed.

Lemma outerMBTs (r : seq L) (P: pred L) (Vs Us : forall i : L, 'H[H]_[set i]) : 
  (\ten_(i <- r | P i) '|Vs i>) \o (\ten_(i <- r | P i) '<Us i|) 
  = \ten_(i <- r | P i) ('|Vs i> \o '<Us i|).
Proof. by rewrite outerMBT. Qed.

Lemma innerMBTs (r : seq L) (P: pred L) (Vs Us: forall i : L, 'H[H]_[set i]) : 
uniq r ->
(\ten_(i <- r | P i) '<Vs i|) \o (\ten_(i <- r | P i) '|Us i>) 
= (\prod_(i <- r | P i) [<Vs i ; Us i>])%:D.
Proof. by move=>ur; rewrite innerMBT// =>i j _ _; rewrite disjoint1X inE. Qed.

End ExtraDiracTheory.

(* here we give the relation between tenvm tenfm and \ten_s *)
(* they are indeed the same, without any conditions *)
Section BigTenLfun.
Context (L : finType) (H : L -> chsType).

Lemma ketd_Hnd_eq (x y : Hnd H) : x = y -> '| of_Hnd x > = '| of_Hnd y >.
Proof. by move=>P; move: (eq_HndP P)=><-; rewrite ketd_cast. Qed.
Lemma lind_Fnd_eq (x y : Fnd H) : x = y -> '[ of_Fnd x ] = '[ of_Fnd y ].
Proof. by move=>P; move: (eq_FndP P)=><-; rewrite lind_cast. Qed.
Lemma ketBT_Hnd (I : Type) (r : seq I) (P : pred I) 
  (s : I -> {set L}) (v : forall i : I, 'H[H]_(s i)) :
    \ten_(i <- r | P i) '|v i> = '| (\tenv_(i <- r | P i) (v i))%FND >.
Proof.
elim/big_rec2: _; first by rewrite bigd ketd_lin /v2f outp_dv0 lindI1.
by move=>i y1 y2 _; rewrite bigd=>->; rewrite /Hnd_ten ketdT.
Qed.
Lemma linBT_Fnd (I : Type) (r : seq I) (P : pred I) 
  (s t : I -> {set L}) (v : forall i : I, 'F[H]_(s i, t i)) :
    \ten_(i <- r | P i) '[v i] = '[ (\tenf_(i <- r | P i) (v i))%FND ].
Proof.
elim/big_rec2: _; first by rewrite bigd/= lindI1.
by move=>i y1 y2 _; rewrite bigd=>->; rewrite /Fnd_ten lindT.
Qed.

Lemma tenvm_correct (J : finType) (s : J -> {set L}) 
  (v : forall j : J, 'H[H]_(s j)) :
    \ten_j '|v j> = '|tenvm v>.
Proof. by rewrite - [tenvm v]to_HndK (ketd_Hnd_eq (to_Hnd_tens _)); apply/ketBT_Hnd. Qed.

Lemma tenfm_correct (J : finType) (s t : J -> {set L}) (v : forall j : J, 'F[H]_(s j, t j)) :
  \ten_j '[ v j ] = '[ tenfm v ].
Proof. by rewrite - [tenfm v]to_FndK (lind_Fnd_eq (to_Fnd_tens _)); apply/linBT_Fnd. Qed.

End BigTenLfun.

Reserved Notation "''ONBD'".
Reserved Notation "''ONBD_' ( F ; S )"      (at level 8, format "''ONBD_' ( F ;  S )").
Reserved Notation "''ONBD[' H ]_ ( F ; S )"     (at level 8).
Reserved Notation "[ 'ONBDirac' 'of' f 'as' g ]" (at level 0, format "[ 'ONBDirac'  'of'  f  'as'  g ]").
Reserved Notation "[ 'ONBDirac' 'of' f ]"  (at level 0, format "[ 'ONBDirac'  'of'  f ]").

Reserved Notation "''NSD'".
Reserved Notation "''NSD_' S"       (at level 8, S at level 2, format "''NSD_' S").
Reserved Notation "''NSD_' ( S )"   (at level 8).
Reserved Notation "''NSD[' H ]_ S"  (at level 8, S at level 2).
Reserved Notation "''NSD[' H ]_ ( S )"     (at level 8).
Reserved Notation "''NSD' ( S )"    (at level 8, format "''NSD' ( S )").
Reserved Notation "[ 'NSD' 'of' f 'as' g ]" (at level 0, format "[ 'NSD'  'of'  f  'as'  g ]").
Reserved Notation "[ 'NSD' 'of' f ]"  (at level 0, format "[ 'NSD'  'of'  f ]").

HB.mixin Record isONBDirac (L : finType) (H : L -> chsType) (F : finType) 
  (S : {set L}) (f : F -> 'D[H]) := {
  is_ketdirac_base : forall i, ketdirac_axiom S (f i);
  onbd_dot : forall i j, (f i)^A \o (f j) = (i == j)%:R%:D;
  onbd_card : #|F| = dim 'H[H]_S;
}.

#[short(type="onbdType")]
HB.structure Definition ONBDirac (L : finType) (H : L -> chsType) (F : finType) (S : {set L}) :=
  { f of @isONBDirac L H F S f}.

Notation "''ONBD[' H ]_ ( F ; S )" := (@onbdType _ H F S) : type_scope.
Notation "''ONBD_' ( F ; S )" := ('ONBD[_]_(F;S)) : type_scope.
Notation "''ONBD'" := ('ONBD_(_;_)) (only parsing) : type_scope.
Module ONBDiracExports.
#[deprecated(since="mathcomp 2.0.0", note="Use ONBDirac.clone instead.")]
Notation "[ 'ONBD' 'of' f 'as' g ]" := (@ONBDirac.clone _ _ _ _ f g) : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use ONBDirac.clone instead.")]
Notation "[ 'ONBD' 'of' f ]" := (@ONBDirac.clone _ _ _ _ f _) : form_scope.
End ONBDiracExports.
HB.export ONBDiracExports.

HB.mixin Record isNSDirac (L : finType) (H : L -> chsType) (S : {set L}) (v : 'D[H]) := {
  is_ketdirac_ns : ketdirac_axiom S v;
  nsd_dot : v^A \o v = 1%:D;
}.

#[short(type="nsdType")]
HB.structure Definition NSDirac (L : finType) (H : L -> chsType) (S : {set L}) :=
  { v of @isNSDirac L H S v }.

Notation "''NSD[' H ]_ S" := (@nsdType _ H S) (only parsing) : type_scope.
Notation "''NSD[' H ]_ ( S )" := ('NSD[H]_S)    (only parsing) : type_scope.
Notation "''NSD_' S"  := ('NSD[_]_S) : type_scope.
Notation "''NSD_' ( S )" := ('NSD_S) (only parsing) : type_scope.
Module NSDiracExports.
#[deprecated(since="mathcomp 2.0.0", note="Use NSDirac.clone instead.")]
Notation "[ 'NSD' 'of' f 'as' g ]" := (@NSDirac.clone _ _ _ f g) : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use NSDirac.clone instead.")]
Notation "[ 'NSD' 'of' f ]" := (@NSDirac.clone _ _ _ f _) : form_scope.
End NSDiracExports.
HB.export NSDiracExports.

Section QEONBTheory.
Context {L : finType} (H : L -> chsType).
Variable (F : finType) (S : {set L}) (f : 'ONBD[H]_(F;S)).

Lemma onbdirac_wf i : ketdirac_axiom S (f i).
Proof. by case: f; clear f=>f/=[[]]. Qed.
Canonical onb_wfdirac i := WFDirac_Build (f i) (@onbdirac_wf i).
Canonical onb_ketdirac i := KetDirac_Build (f i) (@onbdirac_wf i).

Lemma onb_innerM i j : (f i)^A \o (f j) = (i == j)%:R%:D.
Proof. by case: f; clear f=>?/=[[]]. Qed.

Lemma onb_innerG i j : (f i)^A \· (f j) = (i == j)%:R%:D.
Proof. by rewrite dotd_mul/= onb_innerM. Qed.

Definition onb2d (G : finType) (onb : 'ONB[H]_(G;S)) i := '|onb i>.
Lemma onb2d_dot G onb i j : (@onb2d G onb i)^A \o (@onb2d G onb j) = (i == j)%:R%:D.
Proof. by rewrite /onb2d ketd_adj innerM onb_dot. Qed.
Lemma onb2d_ket G onb i : ketdirac_axiom S (@onb2d G onb i).
Proof. apply: is_ketdirac. Qed.
HB.instance Definition _ (G : finType) (onb : 'ONB[H]_(G;S)) :=
  isONBDirac.Build L H G S (@onb2d G onb) (@onb2d_ket G onb) 
    (@onb2d_dot G onb) (@onb_card _ _ onb).
(* Canonical onb2d_qonbasis G onb := ONBDket (@onb2d G onb) (@onb2d_dot G onb) (onb_card onb). *)

Definition d2onb i := d2v S (f i).
Lemma d2onb_dot i j : [< d2onb i ; d2onb j >] = (i == j)%:R.
Proof. by apply/(@numd_inj _ H); rewrite /d2onb -innerM -ketd_adj !d2vK onb_innerM. Qed.
HB.instance Definition _ := 
  isONB.Build _ _ d2onb d2onb_dot (@onbd_card _ _ _ _ f).

Lemma sumonb_outerM : \sum_i ((f i) \o (f i)^A) = \1_S.
Proof.
move: (sumonb_out d2onb)=><-/=.
rewrite linear_sum/=; apply eq_bigr=>i _.
by rewrite -outerM /d2onb -ketd_adj !d2vK.
Qed.

Lemma sumonb_outerG : \sum_i (f i) \· (f i)^A = \1_S.
Proof. by rewrite -sumonb_outerM; apply eq_bigr=>i _; rewrite dotd_mul. Qed.

Lemma onb_vecM (v : 'Ket_S) : (v : 'D) = \sum_i ((f i)^A \o v) \· f i.
Proof.
rewrite -d2vK {1}(onb_vec d2onb (d2v S v)).
rewrite linear_sum; apply eq_bigr=>i _/=.
by rewrite linearZ/= -numdGl /d2onb -innerM -ketd_adj !d2vK.
Qed.

Lemma onb_vecG (v : 'Ket_S) : (v : 'D) = \sum_i ((f i)^A \· v) \· f i.
Proof. by rewrite {1}onb_vecM; apply eq_bigr=>i _; rewrite dotd_mul. Qed.

Lemma onb_lfunM (T : {set L}) (e : 'D_(S,T)) : 
  (e : 'D) = \sum_i (e \o (f i) \o (f i)^A).
Proof.
rewrite -[LHS]muldI -sumonb_outerM linear_sum/=.
by apply eq_bigr=>i _/=; rewrite muldA.
Qed.

Lemma onb_lfunM2 (e : 'D_S) : 
  (e : 'D) = \sum_i \sum_j ((f j)^A \o e \o (f i)) \· ((f j) \o (f i)^A).
Proof.
rewrite {1}onb_lfunM; apply eq_bigr=>i _/=.
rewrite [e \o f i]onb_vecM/= linear_suml; apply eq_bigr=>j _/=.
by rewrite !muldA -d2cK/= !numdGl muldZl.
Qed.

Canonical nsd_wfdirac (v : 'NSD[H]_S) := WFDirac_Build v (is_ketdirac_ns (s := v)).
Canonical nsd_ketdirac (v : 'NSD[H]_S) := KetDirac_Build v (is_ketdirac_ns (s := v)).

Lemma nsd_innerM (v : 'NSD[H]_S) : v^A \o v = 1%:D.
Proof. by case: v=>/=?[[]]. Qed.

Lemma nsd_innerG (v : 'NSD[H]_S) : v^A \· v = 1%:D.
Proof. by rewrite dotd_mul/= nsd_innerM. Qed.

Lemma onbd_ns i : (f i)^A \o (f i) = 1%:D.
Proof. by rewrite onb_innerM eqxx. Qed.
HB.instance Definition _ i := isNSDirac.Build L H S (f i) is_ketdirac (@onbd_ns i).

Lemma ketns_innerM (v : 'NS[H]_S) : '|v>^A \o '|v> = 1%:D.
Proof. by rewrite ketd_adj innerM ns_dot. Qed.
HB.instance Definition _ (v : 'NS[H]_S) := isNSDirac.Build L H S 
  '|v> is_ketdirac (ketns_innerM v).

End QEONBTheory.

Section DiracVOrder.
Context {L : finType} (H : L -> chsType).
Implicit Type (f g h: 'D[H]) (S T W : {set L}).
(* all non-diag are 0, all diag psd *)

Definition psdd :=
  [qualify A : 'D[H] | 
    [forall S, (A S S \is psdlf) && 
      [forall T, (S == T) || (A S T == 0)]]].
Fact psdd_key : pred_key psdd. Proof. by []. Qed.
Canonical psdd_keyed := KeyedQualifier psdd_key.

Lemma psddP f : reflect ((forall S, (f S S \is psdlf)) /\ 
  (forall S T : {set L}, S != T -> (f S T == 0))) (f \is psdd).
Proof.
apply/(iffP idP); rewrite qualifE.
move=>/forallP P; split=>[S|S T/negPf P3]; move: (P S)=>/andP[P1//].
by move=>/forallP/(_ T); rewrite P3.
move=>[P1 P2]; apply/forallP=>S; apply/andP; split=>//.
by apply/forallP=>T; case: eqP=>//= /eqP; apply P2.
Qed.

Definition led_def f g := (g - f) \is psdd.
(* Definition ltd_def f g := (g != f) && (led_def f g). *)

(* Lemma ltd_def_def : forall f g, ltd_def f g = (g != f) && (led_def f g).
Proof. by rewrite /led_def. Qed. *)

Lemma led_def_anti : antisymmetric led_def.
Proof.
move=>f g=>/andP[/psddP [P1 P2]/psddP [P3 P4]].
apply/diracP=>S T. case E: (S == T).
move: E=>/eqP->; apply/le_anti; move: (P1 T) (P3 T).
by rewrite !diracE !psdlfE !subv_ge0=>->->.
by move: E=>/eqP/eqP/P4; rewrite !diracE subr_eq0=>/eqP.
Qed.

Lemma led_def_refl : reflexive led_def.
Proof.
move=>x; apply/psddP; split=>[S|S T _].
all: by rewrite !diracE subrr// is_psdlf.
Qed.

Lemma led_def_trans : transitive led_def.
Proof.
move=>f g h=>/psddP[P1 P2]/psddP[P3 P4].
apply/psddP; split=>[S|S T P5].
move: (P1 S) (P3 S); rewrite !diracE !psdlfE !subv_ge0; exact: le_trans.
by move: (P2 _ _ P5) (P4 _ _ P5); rewrite !diracE !subr_eq0=>/eqP->/eqP->.
Qed.

HB.instance Definition _ := Order.Le_isPOrder.Build ring_display 'D[H]
  led_def_refl led_def_anti led_def_trans.

Lemma ged0P f : reflect ((forall S, ((0 : 'End(_)) ⊑ f S S)) /\ 
  (forall S T : {set L}, S != T -> (f S T == 0))) ((0 : 'D) ⊑ f).
Proof. 
apply/(iffP (psddP _)); rewrite subr0=>[[P1 P2]];
by split=>[|//] S; rewrite ?psdlfE// -psdlfE P1.
Qed.

Lemma led_add2rP h f g : f ⊑ g -> (f + h) ⊑ (g + h).
Proof. by rewrite addrC /Order.le/= /led_def opprD addrA addrK. Qed.

Lemma led_pscale2lP (e : C) f g : 0 < e -> f ⊑ g -> (e *: f) ⊑ (e *: g).
Proof.
move=>egt0/psddP[P1 P2]; apply/psddP; split=>[S|S T /P2].
by move: (P1 S); rewrite !psdlfE=>P3; rewrite -scalerBr diracE pscalev_rge0.
by rewrite -scalerBr [in X in _ -> X]diracE=>/eqP->; rewrite scaler0.
Qed.

HB.instance Definition _ := POrderedLmodule_isVOrder.Build C 'D[H]
  led_add2rP led_pscale2lP.

Lemma ltd_ltf f : (0 : 'D) ⊏ f -> 
  exists (S : {set L}), (0 : 'End('H_S)) ⊏ f S S.
Proof.
rewrite lt_def=>/andP[/eqP+/ged0P[P1 P2]].
rewrite not_existsP; apply contra_not=>P3.
apply/diracP=>S T; rewrite diracE.
case E: (S == T); last by apply/eqP/P2; rewrite E.
move: E=>/eqP->; move: (P3 T) (P1 T)=>/negP/negPf.
by rewrite le_eqVlt eq_sym orbC=>->/=/eqP.
Qed.

Lemma pscaled_lge0 f (a : C) : 
  (0 : 'D) ⊏ f -> (0 : 'D) ⊑ a *: f = (0 <= a).
Proof.
move=>P. move: {+}P=>/ltd_ltf[S Ps].
apply/Bool.eq_iff_eq_true; split.
by move=>/ged0P[/(_ S)+ _]; rewrite diracE pscalev_lge0.
by rewrite le0r=>/orP[/eqP->|P1]; 
  rewrite ?scale0r ?lexx// pscalev_rge0//; apply/ltW.
Qed.

HB.instance Definition _ := VOrder_isCan.Build C 'D[H] pscaled_lge0.

End DiracVOrder.

Section DiracVOrderTheory.
Context {L : finType} (H : L -> chsType).
Implicit Type (S T : {set L}).
Local Notation "'0" := (0 : 'D[H]).
Local Notation "a '%:E'" := (a : 'D) (at level 2, left associativity, format "a %:E").

Lemma lin_eq0 S T (f : 'F[H]_(S,T)) : ('[ f ] == 0) = (f == 0).
Proof. by rewrite -(inj_eq (@lind_inj _ _ _ _)) linear0. Qed.

Lemma wf_ge0_eq0 S T (e : 'D[H]_(S,T)) : 
  S != T -> '0 ⊑ e -> e%:E = 0.
Proof.
by move=>P /ged0P[_/(_ S T P)]/eqP; rewrite {2}wfdiracE=>->; rewrite linear0.
Qed.

Lemma wf_gt0_eq0 S T (e : 'D[H]_(S,T)) : 
  S != T -> '0 ⊏ e -> e%:E = 0.
Proof. move=>+/ltW; exact: wf_ge0_eq0. Qed.

Lemma sqr_gef0 S (e : 'D[H]_S) : '0 ⊑ e = (0%:VF ⊑ e S S).
Proof.
apply/Bool.eq_iff_eq_true; split; first by move=>/ged0P[/(_ S)].
move=>P; apply/ged0P; split=>[T|T W PT]; rewrite sqrdiracE.
case E: (S == T); move: E=>/eqP.
by move=>Q; case: T / Q; rewrite lind_id.
move=>/eqP; rewrite eq_sym=>P1; rewrite lind_eq0l//.
rewrite lind_eq0p//=; move: PT; apply contraNN=>/eqP P1.
by inversion P1.
Qed.

Lemma lin_lef S (f g : 'F[H]_S) : '[ f ] ⊑ '[ g ] = (f ⊑ g).
Proof. by rewrite -subv_ge0 -linearB/= sqr_gef0/= lind_id subv_ge0. Qed.

Lemma lin_ltf S (f g : 'F[H]_S) : '[ f ] ⊏ '[ g ] = (f ⊏ g).
Proof. by rewrite !lt_def -subr_eq0 -linearB/= lin_eq0 subr_eq0 lin_lef. Qed.

Lemma lin_gef0 S (f : 'F[H]_S) : '0 ⊑ '[ f ] = (0%:VF ⊑ f).
Proof. by rewrite -lin_lef linear0. Qed.

Lemma lin_gtf0 S (f : 'F[H]_S) : '0 ⊏ '[ f ] = (0%:VF ⊏ f).
Proof. by rewrite -lin_ltf linear0. Qed.

Lemma sqr_lef S (e1 e2 : 'D[H]_S) : (e1%:E ⊑ e2) = (e1 S S ⊑ e2 S S).
Proof. by rewrite {1}sqrdiracE {1}(sqrdiracE e2) lin_lef. Qed.

Lemma sqr_ltf S (e1 e2 : 'D[H]_S) : (e1%:E ⊏ e2) = (e1 S S ⊏ e2 S S).
Proof. by rewrite {1}sqrdiracE {1}(sqrdiracE e2) lin_ltf. Qed.

Lemma tend_id S1 T1 S2 T2 (f : 'D[H]_(S1,T1)) (g : 'D_(S2,T2)) : 
  (f \⊗ g) (S1 :|: S2) (T1 :|: T2) = (f S1 T1 \⊗ g S2 T2)%VF.
Proof. by rewrite {1}wfdiracE  {1}(wfdiracE g) tend_correct lind_id. Qed.

Lemma tend_sqr_id S T (f : 'D[H]_S) (g : 'D_T) : 
  (f \⊗ g) (S :|: T) (S :|: T) = (f S S \⊗ g T T)%VF.
Proof. by rewrite tend_id. Qed.

Lemma sqr_eqf S (e1 e2 : 'D[H]_S) : (e1%:E == e2) = (e1 S S == e2 S S).
Proof. by rewrite {1}sqrdiracE {1}(sqrdiracE e2) (inj_eq (@lind_inj _ _ _ _)). Qed.

Lemma sqr_eqf0 S (e : 'D[H]_S) : (e%:E == 0) = (e S S == 0).
Proof. by rewrite sqr_eqf/= diracE. Qed.

Ltac simp_sqr := rewrite ?(sqr_lef,sqr_ltf,sqr_eqf0,sqr_eqf)/= 
  ?(tend_sqr_id,lind_id, diracE).

Lemma sqr_gtf0 S (e : 'D[H]_S) : '0 ⊏ e = (0%:VF ⊏ e S S).
Proof. by simp_sqr. Qed.

Lemma sqr_lef0 S (e : 'D[H]_S) : e%:E ⊑ 0 = (e S S ⊑ 0).
Proof. by simp_sqr. Qed.

Lemma sqr_ltf0 S (e : 'D[H]_S) : e%:E ⊏ 0 = (e S S ⊏ 0).
Proof. by simp_sqr. Qed.

Definition sqr_cpf0 := (sqr_gef0, sqr_gtf0, sqr_lef0, sqr_ltf0).

Lemma wf_ge0_ge0 S T (e : 'D[H]_(S,T)) : 
  S = T -> '0 ⊑ e = (0%:VF ⊑ e S S).
Proof.
move=>P; case: T / P e => e.
by rewrite (SqrDirac_BuildE (is_wfdirac (s := e))) sqr_gef0.
Qed.

Lemma wf_gt0_gt0 S T (e : 'D[H]_(S,T)) : 
  S = T -> '0 ⊏ e = (0%:VF ⊏ e S S).
Proof.
move=>P; case: T / P e => e.
by rewrite (SqrDirac_BuildE (is_wfdirac (s := e))) sqr_gtf0.
Qed.

Lemma led0I S : (0 : 'D[H]) ⊑ \1_S.
Proof. by rewrite sqr_gef0/= lind_id lef01. Qed.

Lemma ltd0I S : (0 : 'D[H]) ⊏ \1_S.
Proof. by rewrite sqr_gtf0/= lind_id ltf01. Qed.

Lemma led01 : (0 : 'D[H]) ⊑ :1.
Proof. by rewrite numd1I led0I. Qed.

Lemma ltd01 : (0 : 'D[H]) ⊏ :1.
Proof. by rewrite numd1I ltd0I. Qed.

Lemma sqr_lef1 S (e : 'D[H]_S) : e%:E ⊑ \1_S = (e S S ⊑ \1).
Proof. by simp_sqr. Qed.

Lemma sqr_ltf1 S (e : 'D[H]_S) : e%:E ⊏ \1_S = (e S S ⊏ \1).
Proof. by simp_sqr. Qed.

Lemma sqr_gef1 S (e : 'D[H]_S) : \1_S ⊑ e%:E  = (\1 ⊑ e S S).
Proof. by simp_sqr. Qed.

Lemma sqr_gtf1 S (e : 'D[H]_S) : \1_S ⊏ e%:E  = (\1 ⊏ e S S).
Proof. by simp_sqr. Qed.

Definition sqr_cpf1 := (sqr_lef1, sqr_ltf1, sqr_gef1, sqr_gtf1).

Lemma lin_lef1 S (f : 'F[H]_S) : '[ f ] ⊑ \1_S = (f ⊑ \1).
Proof. by rewrite sqr_lef1/= lind_id. Qed.

Lemma lin_ltf1 S (f : 'F[H]_S) : '[ f ] ⊏ \1_S = (f ⊏ \1).
Proof. by rewrite sqr_ltf1/= lind_id. Qed.

Section tend_order.
Variable (S T : {set L}) (dis : [disjoint S & T]).
Implicit Type (x : 'D[H]_S) (y : 'D[H]_T).

Lemma tend_eq0 x y : x \⊗ y == 0 = (x%:E == 0) || (y%:E == 0).
Proof. by simp_sqr; apply: bregv_eq0. Qed.

Lemma ptend_rge0 x y : '0 ⊏ x -> ('0 ⊑ x \⊗ y) = ('0 ⊑ y).
Proof. by simp_sqr; apply: pbregv_rge0. Qed.

Lemma ptend_lge0 y x : '0 ⊏ y -> ('0 ⊑ x \⊗ y) = ('0 ⊑ x).
Proof. by simp_sqr; apply: pbregv_lge0. Qed.

(* bad !! *)
(* Definition tend_bregVOrderMixin S T dis := 
    bregVOrderMixin (@tend_eq0 S T dis) (ptend_rge0 dis) (ptend_lge0 dis).
Canonical tend_bregVOrderType S T dis := 
  bregVOrderType (@ten_lfun _ _ S S T T) (@tenf_bregVOrderMixin S T dis). *)

Lemma ptend_rgt0 x y : '0 ⊏ x -> ('0 ⊏ x \⊗ y) = ('0 ⊏ y).
Proof. by simp_sqr; apply: pbregv_rgt0. Qed.

Lemma ptend_lgt0 y x : '0 ⊏ y -> ('0 ⊏ x \⊗ y) = ('0 ⊏ x).
Proof. by simp_sqr; apply: pbregv_lgt0. Qed.

Lemma tendI_eq0 x y : x%:E != 0 -> (x \⊗ y == 0) = (y%:E == 0).
Proof. by simp_sqr; apply: bregvI_eq0. Qed.

Lemma tendI x y1 y2 : x%:E != 0 -> x \⊗ y1 = x \⊗ y2 -> y1%:E = y2.
Proof.
by rewrite -!eq_iff; simp_sqr; rewrite !eq_iff=>IH1; apply: (bregvI IH1).
Qed.

Lemma tenId_eq0 y x : y%:E != 0 -> (x \⊗ y == 0) = (x%:E == 0).
Proof. by simp_sqr; apply: bregIv_eq0. Qed.

Lemma tenId y x1 x2 : y%:E != 0 -> x1 \⊗ y = x2 \⊗ y -> x1%:E = x2.
Proof.
by rewrite -!eq_iff; simp_sqr; rewrite !eq_iff=>IH1; apply: (bregIv IH1).
Qed.

Lemma le_ptend2lP x y1 y2 : '0 ⊏ x -> y1%:E ⊑ y2 -> x \⊗ y1 ⊑ x \⊗ y2.
Proof. by simp_sqr; apply: lev_pbreg2lP. Qed.

(* mulr and lev/ltv *)
Lemma le_ptend2l x y1 y2 : '0 ⊏ x -> (x \⊗ y1 ⊑ x \⊗ y2) = (y1%:E ⊑ y2).
Proof. by simp_sqr=>IH; apply: lev_pbreg2l. Qed.

Lemma lt_ptend2l x y1 y2 : '0 ⊏ x -> (x \⊗ y1 ⊏ x \⊗ y2) = (y1%:E ⊏ y2).
Proof. by simp_sqr=>IH; apply: ltv_pbreg2l. Qed.
Definition lte_ptend2l := (le_ptend2l, lt_ptend2l).

Lemma le_ptend2r y x1 x2 : '0 ⊏ y -> (x1 \⊗ y ⊑ x2 \⊗ y) = (x1%:E ⊑ x2).
Proof. by simp_sqr=>IH; apply: lev_pbreg2r. Qed.

Lemma lt_ptend2r y x1 x2 : '0 ⊏ y -> (x1 \⊗ y ⊏ x2 \⊗ y) = (x1%:E ⊏ x2).
Proof. by simp_sqr=>IH; apply: ltv_pbreg2r. Qed.
Definition lte_ptend2r := (le_ptend2r, lt_ptend2r).

Lemma le_ntend2l x y1 y2 : x%:E ⊏ 0 -> (x \⊗ y1 ⊑ x \⊗ y2) = (y2%:E ⊑ y1).
Proof. by simp_sqr=>IH; apply: lev_nbreg2l. Qed.

Lemma lt_ntend2l x y1 y2 : x%:E ⊏ 0 -> (x \⊗ y1 ⊏ x \⊗ y2) = (y2%:E ⊏ y1).
Proof. by simp_sqr=>IH; apply: ltv_nbreg2l. Qed.
Definition lte_ntend2l := (le_ntend2l, lt_ntend2l).

Lemma le_ntend2r y x1 x2 : y%:E ⊏ 0 -> (x1 \⊗ y ⊑ x2 \⊗ y) = (x2%:E ⊑ x1).
Proof. by simp_sqr=>IH; apply: lev_nbreg2r. Qed.

Lemma lt_ntend2r y x1 x2 : y%:E ⊏ 0 -> (x1 \⊗ y ⊏ x2 \⊗ y) = (x2%:E ⊏ x1).
Proof. by simp_sqr=>IH; apply: ltv_nbreg2r. Qed.
Definition lte_ntend2r := (le_ntend2r, lt_ntend2r).

Lemma le_wptend2l x y1 y2 : '0 ⊑ x -> y1%:E ⊑ y2 -> x \⊗ y1 ⊑ x \⊗ y2.
Proof. by simp_sqr=>IH1 IH2; apply: lev_wpbreg2l. Qed.

Lemma le_wntend2l x y1 y2 : x%:E ⊑ 0 -> y1%:E ⊑ y2 -> x \⊗ y2 ⊑ x \⊗ y1.
Proof. by simp_sqr=>IH1 IH2; apply: lev_wnbreg2l. Qed.

Lemma le_wptend2r y x1 x2 : '0 ⊑ y -> x1%:E ⊑ x2 -> x1 \⊗ y ⊑ x2 \⊗ y.
Proof. by simp_sqr=>IH1 IH2; apply: lev_wpbreg2r. Qed.

Lemma le_wntend2r y x1 x2 : y%:E ⊑ 0 -> x1%:E ⊑ x2 -> x2 \⊗ y ⊑ x1 \⊗ y.
Proof. by simp_sqr=>IH1 IH2; apply: lev_wnbreg2r. Qed.

(* Binary forms, for backchaining. *)
Lemma le_ptend2 x1 x2 y1 y2 :
  '0 ⊑ x1 -> '0 ⊑ y1 -> x1%:E ⊑ x2 -> y1%:E ⊑ y2 -> x1 \⊗ y1 ⊑ x2 \⊗ y2.
Proof. by simp_sqr; apply: lev_pbreg2. Qed.

Lemma lt_ptend2 x1 x2 y1 y2 :
  '0 ⊑ x1 -> '0 ⊑ y1 -> x1%:E ⊏ x2 -> y1%:E ⊏ y2 -> x1 \⊗ y1 ⊏ x2 \⊗ y2.
Proof. by simp_sqr; apply: ltv_pbreg2. Qed.

Lemma ptend_rlt0 x y : '0 ⊏ x -> (x \⊗ y ⊏ 0) = (y%:E ⊏ 0).
Proof. by simp_sqr; apply: pbregv_rlt0. Qed.

Lemma ptend_rle0 x y : '0 ⊏ x -> (x \⊗ y ⊑ 0) = (y%:E ⊑ 0).
Proof. by simp_sqr; apply: pbregv_rle0. Qed.

Lemma ntend_rgt0 x y : x%:E ⊏ 0 -> ('0 ⊏ x \⊗ y) = (y%:E ⊏ 0).
Proof. by simp_sqr; apply: nbregv_rgt0. Qed.

Lemma ntend_rge0 x y : x%:E ⊏ 0 -> ('0 ⊑ x \⊗ y) = (y%:E ⊑ 0).
Proof. by simp_sqr; apply: nbregv_rge0. Qed.

Lemma ntend_rlt0 x y : x%:E ⊏ 0 -> (x \⊗ y ⊏ 0) = ('0 ⊏ y).
Proof. by simp_sqr; apply: nbregv_rlt0. Qed.

Lemma ntend_rle0 x y : x%:E ⊏ 0 -> (x \⊗ y ⊑ 0) = ('0 ⊑ y).
Proof. by simp_sqr; apply: nbregv_rle0. Qed.

Lemma ptend_llt0 y x : '0 ⊏ y -> (x \⊗ y ⊏ 0) = (x%:E ⊏ 0).
Proof. by simp_sqr; apply: pbregv_llt0. Qed.

Lemma ptend_lle0 y x : '0 ⊏ y -> (x \⊗ y ⊑ 0) = (x%:E ⊑ 0).
Proof. by simp_sqr; apply: pbregv_lle0. Qed.

Lemma ntend_lgt0 y x : y%:E ⊏ 0 -> ('0 ⊏ x \⊗ y) = (x%:E ⊏ 0).
Proof. by simp_sqr; apply: nbregv_lgt0. Qed.

Lemma ntend_lge0 y x : y%:E ⊏ 0 -> ('0 ⊑ x \⊗ y) = (x%:E ⊑ 0).
Proof. by simp_sqr; apply: nbregv_lge0. Qed.

Lemma ntend_llt0 y x : y%:E ⊏ 0 -> (x \⊗ y ⊏ 0) = ('0 ⊏ x).
Proof. by simp_sqr; apply: nbregv_llt0. Qed.

Lemma ntend_lle0 y x : y%:E ⊏ 0 -> (x \⊗ y ⊑ 0) = ('0 ⊑ x).
Proof. by simp_sqr; apply: nbregv_lle0. Qed.

(* weak and symmetric lemmas *)
Lemma tend_ge0 x y : '0 ⊑ x -> '0 ⊑ y -> '0 ⊑ x \⊗ y.
Proof. by simp_sqr; apply: bregv_ge0. Qed.

Lemma tend_le0 x y : x%:E ⊑ 0 -> y%:E ⊑ 0 -> '0 ⊑ x \⊗ y.
Proof. by simp_sqr; apply: bregv_le0. Qed.

Lemma tend_ge0_le0 x y : '0 ⊑ x -> y%:E ⊑ 0 -> x \⊗ y ⊑ 0.
Proof. by simp_sqr; apply: bregv_ge0_le0. Qed.

Lemma tend_le0_ge0 x y : x%:E ⊑ 0 -> '0 ⊑ y -> x \⊗ y ⊑ 0.
Proof. by simp_sqr; apply: bregv_le0_ge0. Qed.

(* bregv_gt0 with only one case *)

Lemma tend_gt0 x y : '0 ⊏ x -> '0 ⊏ y -> '0 ⊏ x \⊗ y.
Proof. by simp_sqr; apply: bregv_gt0. Qed.

Lemma tend_lt0 x y : x%:E ⊏ 0 -> y%:E ⊏ 0 -> '0 ⊏ x \⊗ y.
Proof. by simp_sqr; apply: bregv_lt0. Qed.

Lemma tend_gt0_lt0 x y : '0 ⊏ x -> y%:E ⊏ 0 -> x \⊗ y ⊏ 0.
Proof. by simp_sqr; apply: bregv_gt0_lt0. Qed.

Lemma tend_lt0_gt0 x y : x%:E ⊏ 0 -> '0 ⊏ y -> x \⊗ y ⊏ 0.
Proof. by simp_sqr; apply: bregv_lt0_gt0. Qed.

Lemma tend_le1 x y : '0 ⊑ x -> '0 ⊑ y 
  -> x%:E ⊑ \1_S -> y%:E ⊑ \1_T -> x \⊗ y ⊑ \1_(S :|: T).
Proof. by move=>P1 P2 P3 P4; rewrite -tendII; apply: le_ptend2=>/=. Qed.

Lemma tend_lt1 x y : '0 ⊑ x -> '0 ⊑ y -> x%:E ⊏ \1_S -> y%:E ⊏ \1_T -> x \⊗ y ⊏ \1_(S :|: T).
Proof. by move=>P1 P2 P3 P4; rewrite -tendII; apply: lt_ptend2=>/=. Qed.
Definition tend_lte1 := (tend_le1, tend_lt1).

Lemma tend_ge1 x y : \1_S ⊑ x -> \1_T ⊑ y -> \1_(S :|: T) ⊑ x \⊗ y.
Proof. by rewrite -tendII=>P1 P2; apply: le_ptend2=>/=[||//|//]; apply: led0I. Qed.

Lemma tend_gt1 x y : \1_S ⊏ x -> \1_T ⊏ y -> \1_(S :|: T) ⊏ x \⊗ y.
Proof. by rewrite -tendII=>P1 P2; apply: lt_ptend2=>/=[||//|//]; apply: led0I. Qed.
Definition tend_gte1 := (tend_ge1, tend_gt1).
Definition tend_cp1 := (tend_lte1, tend_gte1).

End tend_order.

Lemma tend_ge0_le1 S T (P : 'D[H]_S) (Q : 'D_T) :
  [disjoint S & T] ->
  '0 ⊑ P%:E ⊑ \1_S -> '0 ⊑ Q%:E ⊑ \1_T ->
  '0 ⊑ P \⊗ Q  ⊑ \1_(S :|: T).
Proof.
move=>dis/andP[]P1 P2/andP[]P3 P4; apply/andP; split.
by apply: tend_ge0. by rewrite -tendII; apply: le_ptend2=>/=.
Qed.

Lemma tends_ge0_seq (I : eqType) (r : seq I) (R : pred I) (S : I -> {set L})
  (P : forall i, 'D_(S i)) :
  (forall i j, R i -> R j -> i != j -> [disjoint (S i) & (S j)]) -> uniq r ->
  (forall i, R i -> (0 : 'D[H]) ⊑ P i) ->
  '0 ⊑ \ten_(i <- r | R i) P i.
Proof.
move=>IH1+IH2; elim: r=>[|a r IH]; first by rewrite big_nil bigd led01.
rewrite cons_uniq=>/andP[na ur]. rewrite big_cons; case E: (R a).
rewrite bigdE sqrdiracE [X in _\⊗X]sqrdiracE/= tend_correct lin_gef0.
apply: bregv_ge0. apply/bigcup_disjoint_seqP=>i/andP[Pi Ri]. 
apply: IH1=>//. by apply: (notin_in_neq na).
1,2: by rewrite -lin_gef0 -sqrdiracE ?IH2//= IH. by apply IH.
Qed.

Lemma tends_ge0 (I : finType) (R : pred I) (S : I -> {set L})
  (P : forall i, 'D_(S i)) :
  (forall i j, R i -> R j -> i != j -> [disjoint (S i) & (S j)]) ->
  (forall i, R i -> (0 : 'D[H]) ⊑ P i) ->
  '0 ⊑ \ten_(i | R i) P i.
Proof. by move=>IH; apply: tends_ge0_seq=>//; apply: index_enum_uniq. Qed.

Lemma tends_ge0_le1_seq (I : eqType) (r : seq I) (R : pred I) (S : I -> {set L})
  (P : forall i, 'D_(S i)) :
  (forall i j, R i -> R j -> i != j -> [disjoint (S i) & (S j)]) -> uniq r ->
  (forall i, R i -> (0 : 'D[H]) ⊑ (P i : 'D) ⊑ \1_(S i)) ->
  '0 ⊑ \ten_(i <- r | R i) P i ⊑ \1_(\bigcup_(i <- r | R i) S i).
Proof.
move=>IH1+IH2; elim: r=>[|a r IH]; first by rewrite !big_nil bigd led01 numd1I/=.
rewrite cons_uniq=>/andP[na ur]. rewrite !big_cons; case E: (R a).
rewrite bigdE. apply: tend_ge0_le1.
apply/bigcup_disjoint_seqP=>i/andP[Pi Ri]. apply: IH1=>//. by apply: (notin_in_neq na).
by apply IH2. all: by apply : IH.
Qed.

Lemma tends_ge0_le1 (I : finType) (r : seq I) (R : pred I) (S : I -> {set L})
  (P : forall i, 'D_(S i)) :
  (forall i j, R i -> R j -> i != j -> [disjoint (S i) & (S j)]) ->
  (forall i, R i -> (0 : 'D[H]) ⊑ (P i : 'D) ⊑ \1_(S i)) ->
  '0 ⊑ \ten_(i | R i) P i ⊑ \1_(\bigcup_(i | R i) S i).
Proof. move=>IH; apply: tends_ge0_le1_seq=>//; apply: index_enum_uniq. Qed.


End DiracVOrderTheory.