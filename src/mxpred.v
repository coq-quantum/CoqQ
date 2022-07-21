(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra perm.
Require Import mxred forms spectral.
From mathcomp.analysis Require Import boolp.

(* -------------------------------------------------------------------- *)
Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

(* -------------------------------------------------------------------- *)
Local Open Scope ring_scope.

Import Order.TTheory GRing.Theory Num.Theory.

(****************************************************************************)
(* This file is about the predicate of matrix                               *)
(* existing qualifier:                                                      *)
(* qualifier 1: over numDomainType, 'M_(n,m)                                *)
(* realmx posmx nnegmx :=: each elements is Num.real/pos/neg/nneg           *)
(* qualifier 0: over numClosedFieldType, 'M_n                               *)
(* note that          map_mx conjC M = M^*m           M^*t := M^T^*m        *)
(*            normalmx :=: M *m M^*t == M^*t *m M                           *)
(*           unitarymx :=: M *m M^*t == 1%:M      (isometry when not square)*)
(* hermitianmx (epa: bool) (theta: R -> R) :=:                              *)
(*                         M == (-1) ^+ eps *: map_mx theta M^T             *)
(*               symmx :=: M == M^T      (hermitianmx _ false idfun)        *)
(*              hermmx :=: M == M^*t      (hermitianmx _ false conjC)       *)
(* pred: over comUnitRingType, 'M_n                                         *)
(*              unitmx :=: \det M \is a GRing.unit                          *)
(*                         also means that M is full rank, M is invertible  *)
(* new quanlifier defined in this file : 'M_n                               *)
(*              boolmx :=: [forall i, forall j, M i j == 0 || M i j == 1]   *)
(*              uintmx :=: [forall i, forall j, 0 <= M i j <= 1 ]           *)
(*              diagmx :=: [forall i, forall j, i != j ==> M i j == 0]      *)
(*               psdmx :=: M \is hermmx && spectral_diag M \is nnegmx       *)
(*                         positive semi-definite matrix                    *)
(*                pdmx :=: M \is hermmx && spectral_diag M \is posmx        *)
(*                         positive definite matrix                         *)
(*               obsmx :=: M \is hermmx && spectral_diag M \is uintmx       *)
(*                         observable; eigenvalues between 0 and 1          *)
(*               denmx :=: M \is psdmx && \tr M <= 1                        *)
(*                         partial density operators                        *)
(*              den1mx :=: M \is psdmx && \tr M == 1                        *)
(*                         density operators                                *)
(*              projmx :=: M \is hermmx && spectral_diag M \is boolmx       *)
(*                         projection/projective matrix                     *)
(*             proj1mx :=: M \is projmx && rank M == 1                      *)
(****************************************************************************)
(* Hierarchy of predicates                                                  *)
(* realmx --> nnegmx --|--> posmx                                           *)
(*                     |--> uintmx --> boolmx                               *)
(* symmx --> diagmx                                                         *)
(* unitmx --> unitarymx                                                     *)
(* normalmx --|--> unitarymx                                                *)
(*            |--> diagmx                                                   *)
(*            |--> hermmx --> psdmx --|--> pdmx                             *)
(*                                    |--> denmx --|--> projmx --> proj1mx  *)
(*                                                  |--> den1mx             *)
(*                                                  |--> obsmx              *)
(* den1mx --> proj1mx                                                       *)
(* obsmx --> projmx                                                         *)
(****************************************************************************)
(* Defining Types                                                           *)
(* realmx : closed under unitring                                           *)
(* hermmx : closed under lmod                                               *)
(* psdmx : closed under addr                                                *)
(* unitarymx : closed under *m                                              *)
(****************************************************************************)

(* -------------------------------------------------------------------- *)
(* definition of qualifiers *)

Section ConjAdjmx.
Variable (R : numClosedFieldType) (m n : nat).

Definition conjmx (M : 'M[R]_(m,n)) := 
    (map_mx (GRing.RMorphism.apply conjC) M).

Definition adjmx (M : 'M[R]_(m,n)) := 
    (map_mx (GRing.RMorphism.apply conjC) (M ^T)).

Lemma conjmxE M : conjmx M = (map_mx (GRing.RMorphism.apply conjC) M).
Proof. by []. Qed.
Lemma adjmxE M : adjmx M = (map_mx (GRing.RMorphism.apply conjC) (M ^T)).
Proof. by []. Qed.

End ConjAdjmx.

Notation "M ^*m" := (conjmx M) (at level 8, format "M ^*m").
Notation "M ^*t" := (adjmx M) (at level 8, format "M ^*t").

Section ConjAdjmxTheory.
Variable (R : numClosedFieldType).

Lemma conjmx_is_antilinear {m n} : linear_for (conjC \; *:%R) (@conjmx R m n).
Proof. 
move=>a A B. apply/matrixP=>i j.
by rewrite !mxE raddfD/= rmorphM.
Qed.
Canonical conjmx_antilinear m n := Linear (@conjmx_is_antilinear m n).

Lemma conjmx_is_additive {m n} : additive (@conjmx R m n).
Proof. exact: linearB. Qed.
Canonical conjmx_additive m n := Additive (@conjmx_is_additive m n).

Lemma conjmx_is_multiplicative {m } : multiplicative (@conjmx R m.+1 m.+1).
Proof. split.
- move=> A B; apply/matrixP=> i j; rewrite !mxE rmorph_sum.
  by apply: eq_bigr=> /= k _; rewrite rmorphM /= !mxE.
- by apply/matrixP=> i j; rewrite !mxE conjC_nat.
Qed.

Canonical conjmx_rmorphism {m} := AddRMorphism (@conjmx_is_multiplicative m.+1).

Lemma conjmxD {m n} (A B: 'M[R]_(m, n)) : (A + B)^*m = A^*m + B^*m.
Proof. exact: linearD. Qed.

Lemma conjmxZ {m n} (c : R) (A : 'M[R]_(m, n)) : (c *: A)^*m = c^* *: A^*m.
Proof. exact: linearZ. Qed.

Lemma conjmxP {m n} (c: R) (A B: 'M[R]_(m, n)) : 
  (c *: A + B)^*m = c^* *: A^*m + B^*m.
Proof. exact: linearP. Qed.

(*different from rmorphM since the dimension is not the same *)
Lemma conjmxM {m n p} (A: 'M[R]_(m, n)) (B: 'M[R]_(n, p)) :
  (A *m B)^*m = A^*m *m B^*m.
Proof.
apply/matrixP =>i j; rewrite /conjmx !mxE rmorph_sum.
by apply eq_bigr => // k _; rewrite !mxE rmorphM.
Qed.

Lemma conjmxK {m n} : involutive (@conjmx R m n).
Proof. by move=> A; apply/matrixP=> i j; rewrite !mxE conjCK. Qed.

Lemma conjmx_inj {m n} : injective (@conjmx R m n).
Proof. exact (inv_inj conjmxK). Qed.

Lemma conjmx_eq0  m n (A : 'M[R]_(m, n)) : (A^*m == 0) = (A == 0).
Proof. by apply raddf_eq0; apply conjmx_inj. Qed.

Lemma det_conj {m} (M : 'M[R]_m) : \det M^*m = (\det M)^*.
Proof.
rewrite rmorph_sum; apply: eq_bigr=> /= s _.
rewrite rmorphM rmorphX /= rmorphN conjC1; congr (_ * _).
by rewrite rmorph_prod; apply: eq_bigr=> /= i _; rewrite mxE.
Qed.

Lemma conjmx_scale m (a : R) : (a%:M : 'M[R]_m)^*m = (a^*)%:M.
Proof. by apply/matrixP=>i j; rewrite !mxE rmorphMn. Qed.

Lemma conjmx1 m : (1%:M : 'M[R]_m)^*m = 1%:M.
Proof. by rewrite conjmx_scale conjC1. Qed.

(* ==================================================================== *)

Lemma adjmxEr {m n : nat} (M : 'M[R]_(m, n)) : M^*t = M^T^*m.
Proof. by []. Qed.

Lemma adjmxEl {m n : nat} (M : 'M[R]_(m, n)) : M^*t = M^*m^T.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma adjmx_is_antilinear {m n} : linear_for (conjC \; *:%R) (@adjmx R m n).
Proof. by move=>a A B; rewrite !adjmxEl linearP/= linearP/=. Qed.
Canonical adjmx_antilinear m n := Linear (@adjmx_is_antilinear m n).

Lemma adjmx_is_additive {m n} : additive (@adjmx R m n).
Proof. exact: linearB. Qed.
Canonical adjmx_additive m n := Additive (@adjmx_is_additive m n).

Lemma adjmxD {m n} (A B: 'M[R]_(m, n)) : (A + B)^*t = A^*t + B^*t.
Proof. exact: linearD. Qed.

Lemma adjmxZ {m n} (c: R) (A : 'M[R]_(m, n)) : (c *: A)^*t = c^* *: A^*t.
Proof. exact: linearZ. Qed.

Lemma adjmxP {m n} (c: R) (A B: 'M[R]_(m, n)) : 
  (c *: A + B)^*t = c^* *: A^*t + B^*t.
Proof. exact: linearP. Qed.

Lemma adjmxM {m n p} (A: 'M[R]_(m, n)) (B: 'M[R]_(n, p)) :
  (A *m B)^*t = B^*t *m A^*t.
Proof. by rewrite !adjmxEl conjmxM trmx_mul. Qed.

Lemma adjmxK {m n : nat} : cancel (@adjmx R m n) (@adjmx R n m).
Proof. by move=> M; rewrite adjmxEl adjmxEr conjmxK trmxK. Qed.

Lemma adjmx_inj {m n} : injective (@adjmx R m n).
Proof. by move=> M N P; rewrite -(adjmxK M) -(adjmxK N) P. Qed.

Lemma adjmx_eq0  m n (A : 'M[R]_(m, n)) : (A^*t == 0) = (A == 0).
Proof. by apply raddf_eq0; apply adjmx_inj. Qed.

Lemma det_adj {m : nat} (M : 'M[R]_m) : \det M^*t = (\det M)^*.
Proof. by rewrite adjmxEl det_tr det_conj. Qed.

Lemma adjmx_scale m (a : R) : (a%:M : 'M[R]_m)^*t = (a^*)%:M.
Proof. by apply/matrixP=>i j; rewrite !mxE rmorphMn eq_sym. Qed.

Lemma adjmx1 m : (1%:M : 'M[R]_m)^*t = 1%:M.
Proof. by rewrite adjmx_scale conjC1. Qed.

End ConjAdjmxTheory.

Section MxCast.
Variable (R: numClosedFieldType).
Lemma adjmx_cast  m n m' n' (eqS: (m = m') * (n = n')) 
  (A: 'M[R]_(m,n)) : (castmx eqS A)^*t = castmx (eqS.2,eqS.1) (A^*t).
Proof. by rewrite /adjmx trmx_cast map_castmx. Qed.

Lemma conjmx_cast m n m' n' (eqS: (m = m') * (n = n')) 
  (A: 'M[R]_(m,n)) : (castmx eqS A)^*m = castmx eqS (A^*m).
Proof. exact: map_castmx. Qed.

Lemma adjmx_castV m n m' n' (eqS: (n = n') * (m = m')) 
(A: 'M[R]_(m,n)) : castmx eqS (A^*t) = (castmx (eqS.2,eqS.1) A)^*t.
Proof. by rewrite /adjmx trmx_cast map_castmx. Qed.

End MxCast.

Section PredMxDef.
Context {R : numDomainType} (m n : nat).

Definition realmx := (@mxOver m n R Num.real).
Fact realmx_key : pred_key realmx. Proof. by []. Qed.
Canonical realmx_keyed := KeyedQualifier realmx_key.

Lemma realmxP (A : 'M[R]_(m, n)) :
  reflect (forall i j, A i j \is Num.real) (A \is a realmx).
Proof. exact/'forall_'forall_idP. Qed.

Definition posmx := (@mxOver m n R Num.pos).
Fact posmx_key : pred_key posmx. Proof. by []. Qed.
Canonical posmx_keyed := KeyedQualifier posmx_key.

Lemma posmxP (A : 'M[R]_(m, n)) :
  reflect (forall i j, A i j \is Num.pos) (A \is a posmx).
Proof. exact/'forall_'forall_idP. Qed.

Definition nnegmx := (@mxOver m n R Num.nneg).
Fact nnegmx_key : pred_key nnegmx. Proof. by []. Qed.
Canonical nnegmx_keyed := KeyedQualifier nnegmx_key.

Lemma nnegmxP (A : 'M[R]_(m, n)) :
  reflect (forall i j, A i j \is Num.nneg) (A \is a nnegmx).
Proof. exact/'forall_'forall_idP. Qed.

Definition uintmx := (@mxOver m n R (fun x=> 0 <= x <= 1)).
Fact uintmx_key : pred_key uintmx. Proof. by []. Qed.
Canonical uintmx_keyed := KeyedQualifier uintmx_key.

Lemma uintmxP (A : 'M[R]_(m, n)) :
  reflect (forall i j, 0 <= A i j <= 1) (A \is a uintmx).
Proof. exact/'forall_'forall_idP. Qed.

Definition boolmx := (@mxOver m n R (fun x=> (x == false%:R) || (x == true%:R))).
Fact boolmx_key : pred_key boolmx. Proof. by []. Qed.
Canonical boolmx_keyed := KeyedQualifier boolmx_key.

Lemma boolmxP (A : 'M[R]_(m, n)) :
  reflect (forall i j, (A i j == 0) || (A i j == 1)) (A \is a boolmx).
Proof. exact/'forall_'forall_idP. Qed.

End PredMxDef.

Arguments realmx {R m n}.
Arguments posmx {R m n}.
Arguments nnegmx {R m n}.
Arguments uintmx {R m n}.
Arguments boolmx {R m n}.
Arguments unitarymx {C m n}.
Arguments normalmx {C n}.

(* -------------------------------------------------------------------- *)


Section SPredMxDef.
Context {R : numClosedFieldType} (n : nat).

Definition hermmx := (@hermitianmx R n false conjC).
Fact hermmx_key : pred_key hermmx. Proof. by []. Qed.
Canonical hermmx_keyed := KeyedQualifier hermmx_key.

Lemma hermmxP (A : 'M[R]_n) :
  reflect (A = A^*t) (A \is hermmx).
Proof. 
apply (iffP (is_hermitianmxP _ _ A)); by rewrite expr0 scale1r.
Qed.

Definition symmx := (@hermitianmx R n false idfun).
Fact symmx_key : pred_key symmx. Proof. by []. Qed.
Canonical symmx_keyed := KeyedQualifier symmx_key.

Lemma symmxP (A : 'M[R]_n) :
  reflect (A = A^T) (A \is symmx).
Proof. 
by apply (iffP (is_hermitianmxP _ _ A)); rewrite expr0 scale1r map_mx_id.
Qed.

Definition diagmx := 
    [qualify A : 'M[R]_n | is_diag_mx A].
Fact diagmx_key : pred_key diagmx. Proof. by []. Qed.
Canonical diagmx_keyed := KeyedQualifier diagmx_key.

Lemma diagmxP (A : 'M[R]_n) :
  reflect (forall i j, (i != j) -> A i j = 0) (A \is diagmx).
Proof. by apply is_diag_mxP. Qed.

(* normalmx unitarymx unitmx already exists *)
Lemma unitarymxPV (A : 'M[R]_n) : 
  reflect (A ^*t *m A = 1%:M) (A \is unitarymx).
Proof. rewrite -{2}(adjmxK A) adjmxE -trmxC_unitary; apply: unitarymxP. Qed.

Definition psdmx :=
  [qualify A : 'M[R]_n | (A \is hermmx) && ((spectral_diag A) \is a nnegmx)].
Fact psdmx_key : pred_key psdmx. Proof. by []. Qed.
Canonical psdmx_keyed := KeyedQualifier psdmx_key.

Lemma psdmxP (A : 'M[R]_n) : 
  reflect ((A \is hermsymmx) /\ ((spectral_diag A) \is a nnegmx)) (A \is psdmx).
Proof. by apply (iffP andP). Qed.

Definition pdmx :=
  [qualify A : 'M[R]_n | (A \is hermmx) && ((spectral_diag A) \is a posmx)].
Fact pdmx_key : pred_key pdmx. Proof. by []. Qed.
Canonical pdmx_keyed := KeyedQualifier pdmx_key.

Lemma pdmxP (A : 'M[R]_n) : 
  reflect ((A \is hermmx) /\ ((spectral_diag A) \is a posmx)) (A \is pdmx).
Proof. by apply (iffP andP). Qed.

Definition denmx :=
  [qualify A : 'M[R]_n | (A \is psdmx) && (\tr A <= 1)].
Fact denmx_key : pred_key denmx. Proof. by []. Qed.
Canonical denmx_keyed := KeyedQualifier denmx_key.

Lemma denmxP (A : 'M[R]_n) : 
  reflect ((A \is psdmx) /\ (\tr A <= 1)) (A \is denmx).
Proof. by apply (iffP andP). Qed.

Definition den1mx :=
  [qualify A : 'M[R]_n | (A \is psdmx) && (\tr A == 1)].
Fact den1mx_key : pred_key den1mx. Proof. by []. Qed.
Canonical den1mx_keyed := KeyedQualifier den1mx_key.

Lemma den1mxP (A : 'M[R]_n) : 
  reflect ((A \is psdmx) /\ (\tr A == 1)) (A \is den1mx).
Proof. by apply (iffP andP). Qed.

Definition obsmx :=
  [qualify A : 'M[R]_n | (A \is hermmx) && ((spectral_diag A) \is a uintmx)].
Fact obsmx_key : pred_key obsmx. Proof. by []. Qed.
Canonical obsmx_keyed := KeyedQualifier obsmx_key.

Lemma obsmxP (A : 'M[R]_n) : 
  reflect ((A \is hermmx) /\ ((spectral_diag A) \is a uintmx)) (A \is obsmx).
Proof. by apply (iffP andP). Qed.

Definition projmx :=
  [qualify A : 'M[R]_n | (A \is hermmx) && ((spectral_diag A) \is a boolmx)].
Fact projmx_key : pred_key projmx. Proof. by []. Qed.
Canonical projmx_keyed := KeyedQualifier projmx_key.

Lemma projmxP (A : 'M[R]_n) : 
  reflect ((A \is hermmx) /\ ((spectral_diag A) \is a boolmx)) (A \is projmx).
Proof. by apply (iffP andP). Qed.

Definition proj1mx :=
  [qualify A : 'M[R]_n | (A \is projmx) && (\rank A == 1%N)].
Fact proj1mx_key : pred_key proj1mx. Proof. by []. Qed.
Canonical proj1mx_keyed := KeyedQualifier proj1mx_key.

Lemma proj1mxP (A : 'M[R]_n) : 
  reflect ((A \is projmx) /\ (\rank A == 1%N)) (A \is proj1mx).
Proof. by apply (iffP andP). Qed.

End SPredMxDef.

Arguments hermmx {R n}.
Arguments symmx {R n}.
Arguments diagmx {R n}.
Arguments psdmx {R n}.
Arguments pdmx {R n}.
Arguments denmx {R n}.
Arguments den1mx {R n}.
Arguments obsmx {R n}.
Arguments projmx {R n}.
Arguments proj1mx {R n}.

(* -------------------------------------------------------------------- *)
Section RealMxTheory.
Context {R : numDomainType}.

Lemma realmx_real_det m (A : 'M[R]_m) :
  A \is a realmx -> \det A \is Num.real.
Proof.
move=> /realmxP hA; rewrite /determinant rpred_sum //= => i _.
by rewrite rpredM ?rpred_prod // rpredX // rpredN rpred1.
Qed.

Lemma realmx_real_cofactor m (A : 'M[R]_m) i j :
  A \is a realmx -> cofactor A i j \is Num.real.
Proof.
move=> /realmxP hA; rewrite /cofactor rpredM //.
- by rewrite rpredX // rpredN rpred1.
- apply/realmx_real_det; apply/realmxP => i0 j0.
  by rewrite !mxE; apply: hA.
Qed.

Lemma realmx_real_adj m (A : 'M[R]_m) :
  A \is a realmx -> \adj A \is a realmx.
Proof.
by move=> hA; apply/realmxP=> i j; rewrite mxE realmx_real_cofactor.
Qed.

End RealMxTheory.

(* -------------------------------------------------------------------- *)
Section RealMxZmodClosed.
Context {R : numDomainType} (m n : nat).

Fact realmx_zmod_closed : zmod_closed (@realmx R m n).
Proof.
split=> /= [|A B /realmxP hA /realmxP hB];
  by apply/realmxP=> i j; rewrite !mxE (real0, realB).
Qed.

Fact nnegmx_addr_closed : addr_closed (@nnegmx R m n).
Proof.
  split=> /= [|A B /nnegmxP hA /nnegmxP hB];
    apply/nnegmxP=> i j; rewrite nnegrE !mxE.
    by rewrite lexx. by rewrite addr_ge0// -nnegrE.
Qed.

Canonical realmx_addPred  := AddrPred realmx_zmod_closed.
Canonical realmx_oppPred  := OpprPred realmx_zmod_closed.
Canonical realmx_zmodPred := ZmodPred realmx_zmod_closed.
Canonical nnegmx_addPred  := AddrPred nnegmx_addr_closed.

End RealMxZmodClosed.

(* -------------------------------------------------------------------- *)
Section RealMxDivRingClosed.
Context {R : numDomainType} (m : nat).

Fact realmx_divring_closed : divring_closed (@realmx R m.+1 m.+1).
Proof. split=> /=.
- by apply/realmxP=> i j; rewrite mxE realn.
- move=> A B /realmxP hA /realmxP hB; apply/realmxP=> i j.
  by rewrite !mxE rpredD // rpredN.
- move=> A B /realmxP hA /realmxP hB; apply/realmxP=> i j.
  rewrite mxE rpred_sum //= => k _; rewrite rpredM //.
  rewrite /GRing.inv /= /invmx; case: ifP => // unit_B.
  rewrite mxE rpredM // ?rpredV ?realmx_real_det //.
  - by apply/realmxP.
  - by apply/realmxP/realmx_real_adj/realmxP.
Qed.

Canonical realmx_mulrPred     := MulrPred     realmx_divring_closed.
Canonical realmx_semiringPred := SemiringPred realmx_divring_closed.
Canonical realmx_smulrPred    := SmulrPred    realmx_divring_closed.
Canonical realmx_subringPred  := SubringPred  realmx_divring_closed.
Canonical realmx_divringPred  := DivringPred  realmx_divring_closed.

End RealMxDivRingClosed.

Lemma unitarymx_spectralP (C : numClosedFieldType) (m : nat) (A : 'M[C]_m) :
  let P := spectralmx A in let sp := spectral_diag A in
    reflect (A = P ^*t *m diag_mx sp *m P) (A \is normalmx).
Proof. 
rewrite /= adjmxE; apply (iffP idP); move/invmx_unitary: (spectral_unitarymx A)=><-.
apply/orthomx_spectralP. by move/orthomx_spectralP.
Qed.

Section MxPredHierarchy.

Section MxPredElement.
Context {R : numDomainType} (m n : nat).
Implicit Type (M : 'M[R]_(m,n)).

Lemma nnegmx_real M : M \is a nnegmx -> M \is a realmx.
Proof. 
move/nnegmxP=>P; apply/realmxP=>i j; rewrite realE. 
by move: (P i j); rewrite nnegrE=>->.
Qed.

Lemma posmx_nneg M : M \is a posmx -> M \is a nnegmx.
Proof. 
move/posmxP=>P; apply/nnegmxP=>i j; rewrite nnegrE.
by move: (P i j); rewrite posrE le0r=>->; rewrite orbT.
Qed.

Lemma uintmx_nneg M : M \is a uintmx -> M \is a nnegmx.
Proof.
move/uintmxP=>P; apply/nnegmxP=>i j; rewrite nnegrE.
by move: (P i j)=>/andP [-> ].
Qed.

Lemma boolmx_uint M : M \is a boolmx -> M \is a uintmx.
Proof.
move/boolmxP=>P; apply/uintmxP=>i j.
move: (P i j)=>/orP [/eqP -> | /eqP ->];
by rewrite lexx ler01 .
Qed.

Lemma posmx_real M : M \is a posmx -> M \is a realmx.
Proof. by move/posmx_nneg/nnegmx_real. Qed.

Lemma uintmx_real M : M \is a uintmx -> M \is a realmx.
Proof. by move/uintmx_nneg/nnegmx_real. Qed.

Lemma boolmx_nneg M : M \is a boolmx -> M \is a nnegmx.
Proof. by move/boolmx_uint/uintmx_nneg. Qed.

Lemma boolmx_real M : M \is a boolmx -> M \is a realmx.
Proof. by move/boolmx_uint/uintmx_real. Qed.

End MxPredElement.

Section MxPredElement.
Context {R : numClosedFieldType}.
Variable (m: nat).
Implicit Type (M : 'M[R]_m).

Lemma diagmx_sym M : M \is diagmx -> M \is symmx.
Proof.
move/diagmxP=>P. apply/symmxP/matrixP=>i j.
rewrite mxE. case E: (i == j).
by move/eqP: E=>->. by rewrite !P// 1 ?E 1 ?eq_sym 1 ?E.
Qed.

Lemma unitarymx_normal M : M \is unitarymx -> M \is normalmx.
Proof.
move=>P. apply/normalmxP. move: {+}P=>/unitarymxP ->.
by move/unitarymxPV: P=>->.
Qed.

Lemma diagmx_conj M : M \is diagmx -> M ^*t \is diagmx.
Proof.
move/diagmxP=>P. apply/diagmxP=>i j nij.
by rewrite !mxE P ?conjC0// eq_sym.
Qed.

Lemma diagmx_mulC M N : M \is diagmx -> N \is diagmx -> M *m N = N *m M.
Proof.
move=>/diagmxP P /diagmxP Q; apply/matrixP=>i j. 
rewrite !mxE (bigD1 i)// big1/=; last rewrite (bigD1 i)// big1/=.
1, 2: move=> k nki. rewrite P. 3: rewrite Q.
1,2,3,4: by rewrite 1 ?eq_sym 1 ?mul0r.
case E: (i == j). by move/eqP:E=>->; rewrite mulrC.
by rewrite Q 1 ?E// mulr0 P 1 ?E// mulr0.
Qed.

Lemma diagmx_normal M : M \is diagmx -> M \is normalmx.
Proof.
move=>P. move: (diagmx_conj P)=>P1.
apply/normalmxP. rewrite diagmx_mulC//.
Qed.

Lemma hermmx_normal M : M \is hermmx -> M \is normalmx.
Proof. by move/hermmxP=>P; apply/normalmxP; rewrite -adjmxE -?P. Qed.

Lemma psdmx_herm M : M \is psdmx -> M \is hermmx.
Proof. by move/psdmxP=>[->]. Qed.

Lemma pdmx_psdmx M : M \is pdmx -> M \is psdmx.
Proof. 
by move/pdmxP=>[P1 P2]; apply/psdmxP;
  split=>//; apply posmx_nneg. 
Qed.

Lemma obsmx_psd M : M \is obsmx -> M \is psdmx.
Proof. 
by move/obsmxP=>[P1 P2]; apply/psdmxP; 
  split=>//; apply uintmx_nneg.
Qed.

Lemma projmx_obs M : M \is projmx -> M \is obsmx.
Proof. 
by move/projmxP=>[P1 P2]; apply/obsmxP; 
  split=>//; apply boolmx_uint.
Qed.

Lemma proj1mx_proj M : M \is proj1mx -> M \is projmx.
Proof. by move/proj1mxP=>[->]. Qed.


Lemma trace_spectral_diag n (M: 'M[R]_n) : 
  M \is normalmx -> \tr M = \tr (diag_mx (spectral_diag M)).
Proof.
move/unitarymx_spectralP=>{1}->.
rewrite -mulmxA mxtrace_mulC mulmxtVK//.
apply spectral_unitarymx.
Qed.

Lemma diag_mx_real n (M: 'rV[R]_n) : 
  M \is a realmx -> diag_mx M \is a realmx.
Proof.
move/realmxP=>P; apply/realmxP=>i j; rewrite mxE.
case: (i == j); by [rewrite mulr1n P | rewrite mulr0n real0].
Qed.

Lemma diag_mx_nneg n (M: 'rV[R]_n) : 
  M \is a nnegmx -> diag_mx M \is a nnegmx.
Proof.
move/nnegmxP=>P; apply/nnegmxP=>i j; rewrite mxE.
case: (i == j); by [rewrite mulr1n P | rewrite mulr0n nnegrE lexx].
Qed.

Lemma denmx_obs M : M \is denmx -> M \is obsmx.
Proof.
move/denmxP=>[P1 P2].
apply/obsmxP. split. by apply psdmx_herm.
apply/uintmxP=>i j. apply/andP. split.
rewrite -nnegrE. apply/nnegmxP. by move: P1=>/psdmxP [_ ->].
move: P2. rewrite trace_spectral_diag.
by move: P1=>/psdmx_herm/hermmx_normal.
move: P1=>/psdmxP [_ P1].
apply le_trans. rewrite ord1 mxtrace_diag.
have ->: spectral_diag M 0 j = \sum_i (i == j)%:R * (spectral_diag M 0 j).
rewrite (bigD1 j)// big1/=.
by move=>k /negPf ->; rewrite mul0r.
by rewrite !eqxx mul1r addr0.
apply ler_sum=>k _. case: eqP=>[-> | _].
by rewrite mul1r lexx.
by rewrite mul0r -nnegrE; apply/nnegmxP.
Qed.

Lemma den1mx_den M : M \is den1mx -> M \is denmx.
Proof. 
by move/den1mxP=>[P1 /eqP P2]; apply/denmxP; 
  split=>//; rewrite P2 lexx.
Qed.

Lemma denmx_psd M : M \is denmx -> M \is psdmx.
Proof. by move/denmxP=>[->]. Qed.

Lemma normalmx_rank M : M \is normalmx -> \rank M = \rank (diag_mx (spectral_diag M)).
Proof.
move=>/unitarymx_spectralP {1}->.  
rewrite mxrankMfree; last rewrite -mxrank_tr trmx_mul mxrankMfree.
1,2: apply/eqP; rewrite 1 ?mxrank_tr; apply mxrank_unitary;
  rewrite 1 ?trmxC_unitary; do 1 ? apply mxrank_unitary; apply spectral_unitarymx.
by rewrite mxrank_tr.
Qed.

Lemma rank11 (N : 'M[R]_1) : \rank N = (N 0 0 != 0).
Proof. rewrite rank_rV. f_equal.
case: eqP=>[->|]; case: eqP=>//. by rewrite mxE.
move=>P1 P2; exfalso; apply P2. apply/matrixP=>i j. by rewrite !mxE !ord1.
Qed.

Lemma rank_diagmx n (N: 'rV[R]_n) :
  \rank (diag_mx N) = (\sum_i (N 0 i != 0)%R)%N.
Proof.
elim/row_ind : N =>[N|p x N IH].
by rewrite /mxrank !eqxx/= big_ord0.
rewrite diag_mx_row rank_diag_block_mx big_split_ord/= big_ord1.
congr (_ + _)%N. rewrite rank11 !mxE. case: splitP=>j// _. by rewrite ord1 eqxx mulr1n.
rewrite IH. apply eq_bigr=>i _. rewrite mxE. case: splitP=>//= j.
move=>P1; exfalso; move: P1; destruct j=>/= P1; move: i0. by rewrite -P1.
by rewrite !add1n=>/eq_add_S/ord_inj->.
Qed.

Lemma sum_nat_eq1 (I : finType) (F : I -> nat) :
  (\sum_i F i = 1)%N -> exists i, forall j, F j = (i == j).
Proof.
move=>P1. have: exists i, (F i != 0)%N.
rewrite boolp.not_existsP=>P2. move: P1. rewrite big1=>// i _.
move: (P2 i)=>/negP. by rewrite negbK=>/eqP.
move=>[i Pi]. exists i=> j.
have addn_eq1 a b : (a + b = 1 -> (a = 1 /\ b = 0) \/ (a = 0 /\ b = 1))%N.
case: a; case b=>//=.
1,2: move=>n; rewrite ?addn0 ?add0n; case: n=>//. by right. by left.
move=>n n'. by rewrite addSn addnS.
have P3: (F i = 1)%N by move: P1 Pi; rewrite (bigD1 i)//==>/addn_eq1=>[[[//]|[->]]].
case: eqP=>[<-//|/eqP/negPf P2]/=.
move: P1. rewrite (bigD1 i)//= P3 addSn=>/eq_add_S.
rewrite add0n=>/eqP. rewrite sum_nat_eq0=>/forallP/(_ j).
by rewrite eq_sym P2/==>/eqP.
Qed.

Lemma proj1mx_diagP M : M \is proj1mx -> 
  exists i, spectral_diag M = delta_mx 0 i.
Proof.
move/proj1mxP=>[/projmxP[/hermmx_normal/normalmx_rank->]/boolmxP /(_ 0)P1 /eqP].
rewrite rank_diagmx=>/sum_nat_eq1[i P].
exists i. apply/matrixP=>x y. rewrite !mxE !ord1 eqxx/=.
case: eqP. move=>->. move: (P i) (P1 i). rewrite eqxx/=.
by case: eqP=>//= _ _ /eqP->.
move/eqP/negPf=>P2; move: (P y). rewrite [i == _]eq_sym P2.
case: eqP=>//.
Qed.

Lemma proj1mx_den1 M : M \is proj1mx -> M \is den1mx.
Proof.
move=> P. move: {+}P=>/proj1mx_proj/projmx_obs/obsmx_psd=>P1.
apply/den1mxP. split=>//.
rewrite trace_spectral_diag. by move: P1=>/psdmx_herm/hermmx_normal.
move: P=>/proj1mx_diagP P. destruct P.
rewrite H mxtrace_diag (bigD1 x)// big1/=.
by move=>j /negPf njx; rewrite mxE njx andbF.
by rewrite mxE !eqxx addr0.
Qed.

End MxPredElement.
End MxPredHierarchy.

Section ExtraTheory.
Variable (R: numClosedFieldType).

Lemma mx_dot_diag n (M: 'M[R]_n) (u: 'rV[R]_n) : 
  M \is diagmx -> \tr (u *m M *m u^*t) = \sum_i M i i * `|u 0 i| ^+2.
Proof.
move/diagmxP=>Pm.
rewrite trace_mx11 mxE. apply eq_bigr=>i _.
rewrite !mxE (bigD1 i)// big1/=.
by move=> j nji; rewrite Pm// mulr0.
by rewrite addr0 [u 0 i * _]mulrC -mulrA normCK.
Qed.

Lemma mx_dot_diag_mx n (M u: 'rV[R]_n) : 
  \tr (u *m diag_mx M *m u^*t) = \sum_i M 0 i * `|u 0 i| ^+2.
Proof.
move: (diag_mx_is_diag M)=>/mx_dot_diag P. rewrite (P u).
by under eq_bigr do rewrite mxE eqxx mulr1n.
Qed.

Lemma mx_dot_eq0 n (M: 'M[R]_n)  : 
  reflect (forall (u: 'rV[R]_n), \tr (u *m M *m u^*t) = 0) (M == 0).
Proof.
  apply (iffP eqP).
  by move=>-> u; rewrite mulmx0 mul0mx linear0.
  move=>P. apply/matrixP=>i j. rewrite mxE.
  move: (P (delta_mx 0 i)) (P (delta_mx 0 j)) (P (delta_mx 0 i + delta_mx 0 j))
  (P ('i *: (delta_mx 0 i) + delta_mx 0 j)).
  rewrite !mulmxDl !linearD/= !linearZ/= !linearZl/= !linearZ/= => -> => ->.
  rewrite !mulr0 !addr0 !add0r conjCi mulNr.
  move/addr0_eq=> <-. rewrite mulrN opprK -mulrDl trace_mx11 !mxE.
  rewrite (bigD1 j)//= big1.
  by move=>k /negPf nkj; rewrite !mxE nkj andbF conjC0 mulr0.
  rewrite !mxE (bigD1 i)//= big1.
  by move=>k /negPf nkj; rewrite !mxE nkj andbF mul0r.
  rewrite !mxE !eqxx conjC1 mulr1 mul1r !addr0 mulrC.
  move/eqP. rewrite mulIr_eq0. apply/rregP.
  by rewrite -mulr2n mulrn_eq0 negb_or/= neq0Ci.
  by move/eqP.
Qed.

Lemma mx_dot_conj n (M: 'M[R]_n) : 
  forall u : 'rV_n, \tr (u *m M^*t *m u ^*t) = (\tr (u *m M *m u ^*t))^*.
Proof.
move=>u; by rewrite -[in RHS]mxtrace_tr -trace_map_mx -adjmxE
  !adjmxM adjmxK mulmxA.
Qed. 

Lemma hermmx_dot n (M: 'M[R]_n) :
  reflect (forall u: 'rV[R]_n, \tr (u *m M *m u^*t) \is Num.real) (M \is hermmx).
Proof.
apply (iffP (is_hermitianmxP _ _ M)); rewrite expr0 scale1r -adjmxE.
by move=> H u; apply/CrealP; rewrite -mx_dot_conj -H.
move=> H. apply subr0_eq. apply/eqP/mx_dot_eq0=>u.
rewrite mulmxDr mulmxDl linearD/= mulmxN mulNmx linearN/= mx_dot_conj.
move: (H u). move/CrealP=>->. apply addrN.
Qed.

Lemma psdmx_dot n (M: 'M[R]_n)  : 
  reflect (forall u: 'rV[R]_n, \tr (u *m M *m u^*t) \is Num.nneg) (M \is psdmx).
Proof.
apply (iffP (psdmxP M))=>[[Pm Pd] u | P].
move/unitarymx_spectralP: (hermitian_normalmx Pm)=>->.
move: (mx_dot_diag_mx (spectral_diag M) (u *m ((spectralmx M) ^*t))).
rewrite !adjmxM !mulmxA! nnegrE adjmxK =>->.
apply sumr_ge0=> i _; apply mulr_ge0.
  rewrite -nnegrE; move/nnegmxP: Pd=>Pd; apply Pd.
  apply exprn_ge0; apply normr_ge0.
have Pm: M \is hermmx. 
by apply/hermmx_dot=>u; move: (P u); by rewrite nnegrE realE=>->.
split=>//; move/unitarymx_spectralP: (hermitian_normalmx Pm) => P1.
apply/nnegmxP=>i j; rewrite ord1.
move: (P (delta_mx 0 j *m spectralmx M)).
rewrite {2}P1 !adjmxM !mulmxA !mulmxtVK ?(spectral_unitarymx M)//.
rewrite mx_dot_diag_mx (bigD1 j)// big1/=.
  by move=>k /negPf nkj; rewrite !mxE nkj andbF normrE expr0n mulr0.
  by rewrite !mxE !eqxx normrE expr1n mulr1 addr0.
Qed.

Lemma psdmx_bimap_closed_gen n (M: 'M[R]_n) m (A: 'M[R]_(m,n)) : 
  M \is psdmx -> A *m M *m A ^*t \is psdmx.
Proof.
move/psdmx_dot=>P; apply/psdmx_dot=>u.
by move: (P (u *m A)); rewrite adjmxM !mulmxA.
Qed.

Lemma diagmx_nnegmx_psd n (M: 'rV[R]_n) :
  M \is a nnegmx -> diag_mx M \is psdmx.
Proof.
move/nnegmxP=>P. apply/psdmx_dot=>u.
rewrite mx_dot_diag_mx nnegrE.
apply sumr_ge0=>i _; apply mulr_ge0.
  rewrite -nnegrE; apply P.
rewrite exprn_ge0// normr_ge0.
Qed.

Lemma obsmx_psd_eq n (M: 'M[R]_n) : 
  M \is obsmx = (M \is psdmx) && (1%:M - M \is psdmx).
Proof.
apply Bool.eq_true_iff_eq. split.
move/obsmxP=>[Pm Pu].
apply/andP. split. apply/psdmxP. split=>//. by apply uintmx_nneg.
have: (const_mx 1 - spectral_diag M) \is a nnegmx.
apply/nnegmxP=>i j. rewrite !mxE nnegrE subr_ge0.
move/uintmxP: Pu=>Pu.
by move: (Pu i j)=>/andP[_ ->].
move/diagmx_nnegmx_psd/(psdmx_bimap_closed_gen ((spectralmx M) ^*t)).
rewrite adjmxK !linearB/= mulmxBl diag_const_mx mulmx1.
move: (spectral_unitarymx M)=>/unitarymxPV=>->.
by move: (hermitian_normalmx Pm)=>/unitarymx_spectralP <-.
move/andP=>[/psdmxP [P1 P2] /psdmx_dot P3].
apply/obsmxP. split=>//.
apply/uintmxP=>i j. apply/andP. split. by apply/nnegmxP.
move: (P3 (delta_mx i j *m spectralmx M)).
move: (hermitian_normalmx P1)=>/unitarymx_spectralP P4.
rewrite {2}P4 !linearB/= mulmxBl linearB/= !adjmxM !mulmxA mulmx1 
  !mulmxtVK ?(spectral_unitarymx M)// mx_dot_diag_mx (bigD1 j)// big1/=.
  by move=>k /negPf nkj; rewrite !mxE nkj andbF normrE expr0n mulr0.
  rewrite trace_mx11 mxE (bigD1 j)// big1/=.
  by move=>k /negPf nkj; rewrite !mxE nkj andbF mul0r.
  rewrite !mxE ord1 !eqxx/= conjC1 mulr1 normrE expr1n mulr1 !addr0.
  by rewrite nnegrE subr_ge0.
Qed.

Lemma obsmx_dot n (M: 'M[R]_n) : 
  reflect (forall u: 'rV[R]_n, 0 <= \tr (u *m M *m u^*t) <= \tr (u *m u^*t)) (M \is obsmx).
Proof.
rewrite obsmx_psd_eq. apply (iffP idP).
move/andP=>[/psdmx_dot P1 /psdmx_dot P2].
move=>u. move: (P1 u) (P2 u).
2: move=>P; apply/andP; split; apply/psdmx_dot=>u; move: (P u)=>/andP.
all: rewrite !nnegrE 1 ?linearB/= 1 ?mulmx1 1 ?mulmxBl 1 ?linearB/= 1?subr_ge0.
by move=>->-. by move=>[->]. by move=>[_ ->].
Qed.

Lemma hermmx0 n : (0 : 'M[R]_n) \is hermmx.
Proof. by apply/hermmxP; rewrite linear0. Qed.

Lemma psdmx0 n : (0 : 'M[R]_n) \is psdmx.
Proof. by apply/psdmx_dot=>u; rewrite mulmx0 mul0mx linear0 nnegrE lexx. Qed.

Lemma psdmx_eq0 n (M: 'M[R]_n) : M \is psdmx -> - M \is psdmx -> M = 0.
Proof.
  move=>/psdmx_dot Pm /psdmx_dot Pn. apply/eqP/mx_dot_eq0 =>u. apply le_anti.
  rewrite -oppr_ge0 -linearN/= -mulNmx -mulmxN -!nnegrE. by apply/andP.
Qed.

End ExtraTheory.

(* realmx --> nnegmx --|--> posmx                                           *)
(*                     |--> uintmx --> boolmx                               *)
(* symmx --> diagmx                                                         *)
(* unitmx --> unitarymx                                                     *)
(* normalmx --|--> unitarymx                                                *)
(*            |--> diagmx                                                   *)
(*            |--> hermmx --> psdmx --|--> pdmx                             *)
(*                                    |--> obsmx --|--> projmx --> proj1mx  *)
(*                                                 |--> denmx --> den1mx    *)
(* den1mx --> proj1mx                                                        *)


(****************************************************************************)
(* Defining Types                                                           *)
(* hermmx : closed under zmod_closed                                        *)
(* psdmx : closed under addr_closed                                         *)
(* unitarymx : closed under *m                                              *)
(* denmx obsmx : forms CPO                                                 *)
(****************************************************************************)

Definition operator_closed (R: numClosedFieldType) (m n: nat) (S : {pred 'M[R]_(m,n)})
  (op : 'M[R]_(m,n) -> 'M[R]_(m,n) -> 'M[R]_(m,n)) :=
    {in S &, forall A B, op A B \in S}.

Definition mulmx_closed (R: ringType) (m: nat) (S: {pred 'M[R]_m}) :=
  {in S &, forall A B, A *m B \in S}.

Definition bimap_closed (R: numClosedFieldType) (m: nat) (T: {pred 'M[R]_m}) :=
  {in predT & T, forall A B, A *m B *m A ^*t \in T}.

Definition bipred_closed (R: numClosedFieldType) (m: nat) (S T: {pred 'M[R]_m}) :=
  {in S & T, forall A B, A *m B *m A ^*t \in T}.

Definition unitary_closed (R: numClosedFieldType) (m: nat) (S: {pred 'M[R]_m}) :=
  bipred_closed (@unitarymx _ _ _) S.

Section ExtraMxPredClosed.
Context {R : numClosedFieldType} (m : nat).

Fact hermmx_zmod_closed : zmod_closed (@hermmx R m).
Proof. 
split=>[ | A B /hermmxP hA /hermmxP hB]. apply hermmx0.
by apply/hermmxP; rewrite linearD/= linearN/= [in LHS]hA [in LHS]hB.
Qed.

Canonical hermmx_addPred  := AddrPred hermmx_zmod_closed.
Canonical hermmx_oppPred  := OpprPred hermmx_zmod_closed.
Canonical hermmx_zmodPred := ZmodPred hermmx_zmod_closed.

Lemma psdmx_add: operator_closed (@psdmx R m) (+%R).
Proof. 
move=> A B /psdmx_dot hA /psdmx_dot hB. apply/psdmx_dot=>u.
move: (hA u) (hB u). rewrite mulmxDr mulmxDl linearD/= !nnegrE.
by apply ler_paddl.
Qed.

Fact psdmx_addr_closed : addr_closed (@psdmx R m).
Proof. split. apply psdmx0. apply psdmx_add. Qed.

Canonical psdmx_addPred  := AddrPred psdmx_addr_closed.

Fact unitmx_mulmx_closed : mulmx_closed (@unitmx R m).
Proof. by move=>A B; rewrite unitmx_mul=>->=>->. Qed.

Fact unitarymx_mulmx_closed : mulmx_closed (@unitarymx R m m).
Proof. 
move=>A B /unitarymxP hA /unitarymxP hB. apply/unitarymxP.
by rewrite -adjmxE adjmxM mulmxA -[A *m _ *m _]mulmxA hB mulmx1 hA.
Qed.

Fact hermmx_bimap_closed : bimap_closed (@hermmx R m).
Proof.
move=>A B _ /hermmx_dot Pb.
apply/hermmx_dot=>u. move: (Pb (u *m A)).
by rewrite adjmxM !mulmxA.
Qed.

Fact psdmx_bimap_closed : bimap_closed (@psdmx R m).
Proof.
move=>A B _ /psdmx_dot Pb.
apply/psdmx_dot=>u. move: (Pb (u *m A)).
by rewrite adjmxM !mulmxA.
Qed.

Fact denmx_unitary_closed : unitary_closed (@denmx R m).
Proof.
move=>A B /unitarymxPV hA /denmxP [hB tB]. apply/denmxP. split.
apply psdmx_bimap_closed=>//.
by rewrite mxtrace_mulC mulmxA hA mul1mx.
Qed.

Fact den1mx_unitary_closed : unitary_closed (@den1mx R m).
Proof.
move=>A B /unitarymxPV hA /den1mxP [hB tB]. apply/den1mxP. split.
apply psdmx_bimap_closed=>//.
by rewrite mxtrace_mulC mulmxA hA mul1mx.
Qed.

Fact obsmx_unitary_closed : unitary_closed (@obsmx R m).
Proof.
move=>A B /unitarymxP hA /obsmx_dot hB. apply/obsmx_dot => u.
move: (hB (u *m A)).
by rewrite adjmxM -!mulmxA [A *m (A ^*t *m _)]mulmxA hA mul1mx.
Qed.

End ExtraMxPredClosed.

(* -------------------------------------------------------------------- *)
Section RealMxType.
Context {R : numDomainType} (m n : nat).

Variant realmx_t :=
  RealMx (M : 'M[R]_(m, n)) of M \is a realmx.

Coercion realmx_mx (M : realmx_t) :=
  let: RealMx M _ := M in M.

Canonical realmx_subType := Eval hnf in [subType for realmx_mx].

Definition realmx_eqMixin := Eval hnf in [eqMixin of realmx_t by <:].
Canonical  realmx_eqType  := Eval hnf in EqType realmx_t realmx_eqMixin.

Definition realmx_choiceMixin := [choiceMixin of realmx_t by <:].
Canonical  realmx_choiceType  := Eval hnf in ChoiceType realmx_t realmx_choiceMixin.

Lemma realmx_inj : injective realmx_mx. Proof. exact: val_inj. Qed.

Definition realmx_of of phant R := realmx_t.
Identity Coercion type_realmx_of : realmx_of >-> realmx_t.
End RealMxType.

Bind Scope ring_scope with realmx_of.
Bind Scope ring_scope with realmx_t.

Arguments realmx_mx {R m n} M%R.
Arguments realmx_inj {R m n} [A%R B%R] : rename.

Notation "''MR[' R ]_ ( m , n )" := (@realmx_of _ m n (Phant R))
  (at level 8, format "''MR[' R ]_ ( m , n )").

(* -------------------------------------------------------------------- *)
Section RealMxOf.
Context {R : numDomainType} (m n : nat).

Canonical realmx_of_subType    := Eval hnf in [subType    of 'MR[R]_(m, n)].
Canonical realmx_of_eqType     := Eval hnf in [eqType     of 'MR[R]_(m, n)].
Canonical realmx_of_choiceType := Eval hnf in [choiceType of 'MR[R]_(m, n)].
End RealMxOf.

(* -------------------------------------------------------------------- *)
Section RealMxZmod.
Context {R : numDomainType} (m n : nat).

Definition realmx_zmodMixin := [zmodMixin of 'MR[R]_(m, n) by <:].
Canonical realmx_zmodType :=
  Eval hnf in ZmodType 'MR[R]_(m, n) realmx_zmodMixin.
Canonical realmx_of_zmodType :=
  Eval hnf in ZmodType (@realmx_t R m n) realmx_zmodMixin.
End RealMxZmod.

(* -------------------------------------------------------------------- *)
Section RealMxRing.
Context {R : numDomainType} (m : nat).

Definition realmx_ringMixin := [ringMixin of 'MR[R]_(m.+1, m.+1) by <:].
Canonical realmx_ringType :=
  Eval hnf in RingType 'MR[R]_(m.+1, m.+1) realmx_ringMixin.
Canonical realmx_of_ringType :=
  Eval hnf in RingType (@realmx_t R m.+1 m.+1) realmx_ringMixin.
End RealMxRing.

(* -------------------------------------------------------------------- *)
Section RealMxRing.
Context {R : numDomainType} (m : nat).

Definition realmx_unitRingMixin := [unitRingMixin of 'MR[R]_(m.+1, m.+1) by <:].
Canonical realmx_unitRingType :=
  Eval hnf in UnitRingType 'MR[R]_(m.+1, m.+1) realmx_unitRingMixin.
Canonical realmx_of_unitRingType :=
  Eval hnf in UnitRingType (@realmx_t R m.+1 m.+1) realmx_unitRingMixin.
End RealMxRing.

(* -------------------------------------------------------------------- *)
Section HermMxType.
Context {R : numClosedFieldType} (m : nat).

Variant hermmx_t :=
  HermMx (M : 'M[R]_m) of (M \is hermmx).

Coercion hermmx_mx (M : hermmx_t) :=
  let: HermMx M _ := M in M.

Canonical hermmx_subType := Eval hnf in [subType for hermmx_mx].

Definition hermmx_eqMixin := Eval hnf in [eqMixin of hermmx_t by <:].
Canonical  hermmx_eqType  := Eval hnf in EqType hermmx_t hermmx_eqMixin.

Definition hermmx_choiceMixin := [choiceMixin of hermmx_t by <:].
Canonical  hermmx_choiceType  := Eval hnf in ChoiceType hermmx_t hermmx_choiceMixin.

Lemma hermmx_inj : injective hermmx_mx. Proof. exact: val_inj. Qed.

Definition hermmx_of of phant R := hermmx_t.
Identity Coercion type_hermmx_of : hermmx_of >-> hermmx_t.
End HermMxType.

Bind Scope ring_scope with hermmx_of.
Bind Scope ring_scope with hermmx_t.

Arguments hermmx_mx {R m} M%R.
Arguments hermmx_inj {R m} [A%R B%R] : rename.

Notation "''MH[' R ]_ m " := (@hermmx_of _ m (Phant R))
  (at level 8, format "''MH[' R ]_ m").

(* -------------------------------------------------------------------- *)
Section HermMxOf.
Context {R : numClosedFieldType} (m : nat).

Canonical hermmx_of_subType    := Eval hnf in [subType    of 'MH[R]_m].
Canonical hermmx_of_eqType     := Eval hnf in [eqType     of 'MH[R]_m].
Canonical hermmx_of_choiceType := Eval hnf in [choiceType of 'MH[R]_m].
End HermMxOf.

Section HermMxZmod.
Context {R : numClosedFieldType} (m : nat).

Definition hermmx_zmodMixin := [zmodMixin of 'MH[R]_m by <:].
Canonical hermmx_zmodType :=
  Eval hnf in ZmodType 'MH[R]_m hermmx_zmodMixin.
Canonical hermmx_of_zmodType :=
  Eval hnf in ZmodType (@hermmx_t R m) hermmx_zmodMixin.
End HermMxZmod.


(* -------------------------------------------------------------------- *)
Section DenMxType.
Context {R : numClosedFieldType} (m : nat).

Variant denmx_t :=
  DenMx (M : 'M[R]_m) of (M \is denmx).

Coercion denmx_mx (M : denmx_t) :=
  let: DenMx M _ := M in M.

Canonical denmx_subType := Eval hnf in [subType for denmx_mx].

Definition denmx_eqMixin := Eval hnf in [eqMixin of denmx_t by <:].
Canonical  denmx_eqType  := Eval hnf in EqType denmx_t denmx_eqMixin.

Definition denmx_choiceMixin := [choiceMixin of denmx_t by <:].
Canonical  denmx_choiceType  := Eval hnf in ChoiceType denmx_t denmx_choiceMixin.

Lemma denmx_inj : injective denmx_mx. Proof. exact: val_inj. Qed.

Definition denmx_of of phant R := denmx_t.
Identity Coercion type_denmx_of : denmx_of >-> denmx_t.

End DenMxType.

Bind Scope ring_scope with denmx_of.
Bind Scope ring_scope with denmx_t.

Arguments denmx_mx {R m} M%R.
Arguments denmx_inj {R m} [A%R B%R] : rename.

Notation "''MDen[' R ]_ m " := (@denmx_of _ m (Phant R))
  (at level 8, format "''MDen[' R ]_ m").

(* -------------------------------------------------------------------- *)
Section DenMxOf.
Context {R : numClosedFieldType} (m : nat).

Canonical denmx_of_subType    := Eval hnf in [subType    of 'MDen[R]_m].
Canonical denmx_of_eqType     := Eval hnf in [eqType     of 'MDen[R]_m].
Canonical denmx_of_choiceType := Eval hnf in [choiceType of 'MDen[R]_m].

End DenMxOf.


(* -------------------------------------------------------------------- *)
Section ObsMxType.
Context {R : numClosedFieldType} (m : nat).

Variant obsmx_t :=
  ObsMx (M : 'M[R]_m) of (M \is obsmx).

Coercion obsmx_mx (M : obsmx_t) :=
  let: ObsMx M _ := M in M.

Canonical obsmx_subType := Eval hnf in [subType for obsmx_mx].

Definition obsmx_eqMixin := Eval hnf in [eqMixin of obsmx_t by <:].
Canonical  obsmx_eqType  := Eval hnf in EqType obsmx_t obsmx_eqMixin.

Definition obsmx_choiceMixin := [choiceMixin of obsmx_t by <:].
Canonical  obsmx_choiceType  := Eval hnf in ChoiceType obsmx_t obsmx_choiceMixin.

Lemma obsmx_inj : injective obsmx_mx. Proof. exact: val_inj. Qed.

Definition obsmx_of of phant R := obsmx_t.
Identity Coercion type_obsmx_of : obsmx_of >-> obsmx_t.

End ObsMxType.

Bind Scope ring_scope with obsmx_of.
Bind Scope ring_scope with obsmx_t.

Arguments obsmx_mx {R m} M%R.
Arguments obsmx_inj {R m} [A%R B%R] : rename.

Notation "''MObs[' R ]_ m " := (@obsmx_of _ m (Phant R))
  (at level 8, format "''MObs[' R ]_ m").

(* -------------------------------------------------------------------- *)
Section ObsMxOf.
Context {R : numClosedFieldType} (m : nat).

Canonical obsmx_of_subType    := Eval hnf in [subType    of 'MObs[R]_m].
Canonical obsmx_of_eqType     := Eval hnf in [eqType     of 'MObs[R]_m].
Canonical obsmx_of_choiceType := Eval hnf in [choiceType of 'MObs[R]_m].

End ObsMxOf.





