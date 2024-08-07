(* -------------------------------------------------------------------- *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra perm fingroup.
From mathcomp.analysis Require Import -(notations)forms.
Require Import notation mcaextra mcextra spectral.
(* From mathcomp.analysis Require Import boolp signed topology. *)
(* reprove some properties of bigmax; which shouldn't depends on classic logic *)

(* -------------------------------------------------------------------- *)
Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

(* -------------------------------------------------------------------- *)
Local Open Scope ring_scope.

Import Order.Theory GRing.Theory Num.Theory Num.Def.

(******************************************************************************)
(*                       Predicate and Norms of matrix                        *)
(* -------------------------------------------------------------------------- *)
(* existing qualifier:                                                        *)
(* qualifier 1: over numDomainType, 'M_(n,m)                                  *)
(* realmx posmx nnegmx :=: each elements is Num.real/pos/neg/nneg             *)
(* qualifier 0: over numClosedFieldType, 'M_n                                 *)
(* note that          map_mx conjC M = M^*m           M^*t := M^T^*m          *)
(*            normalmx :=: M *m M^*t == M^*t *m M                             *)
(*           unitarymx :=: M *m M^*t == 1%:M      (isometry when not square)  *)
(* hermitianmx (epa: bool) (theta: R -> R) :=:                                *)
(*                         M == (-1) ^+ eps *: map_mx theta M^T               *)
(*               symmx :=: M == M^T      (hermitianmx _ false idfun)          *)
(*              hermmx :=: M == M^*t      (hermitianmx _ false conjC)         *)
(* pred: over comUnitRingType, 'M_n                                           *)
(*              unitmx :=: \det M \is a GRing.unit                            *)
(*                         also means that M is full rank, M is invertible    *)
(* new quanlifier defined in this file : 'M_n                                 *)
(*              boolmx :=: [forall i, forall j, M i j == 0 || M i j == 1]     *)
(*              uintmx :=: [forall i, forall j, 0 <= M i j <= 1 ]             *)
(*              diagmx :=: [forall i, forall j, i != j ==> M i j == 0]        *)
(*               psdmx :=: M \is hermmx && spectral_diag M \is nnegmx         *)
(*                         positive semi-definite matrix                      *)
(*                pdmx :=: M \is hermmx && spectral_diag M \is posmx          *)
(*                         positive definite matrix                           *)
(*               obsmx :=: M \is hermmx && spectral_diag M \is uintmx         *)
(*                         observable; eigenvalues between 0 and 1            *)
(*               denmx :=: M \is psdmx && \tr M <= 1                          *)
(*                         partial density operators                          *)
(*              den1mx :=: M \is psdmx && \tr M == 1                          *)
(*                         density operators                                  *)
(*              projmx :=: M \is hermmx && spectral_diag M \is boolmx         *)
(*                         projection/projective matrix                       *)
(*             proj1mx :=: M \is projmx && rank M == 1                        *)
(******************************************************************************)
(* Hierarchy of predicates                                                    *)
(* realmx --> nnegmx --|--> posmx                                             *)
(*                     |--> uintmx --> boolmx                                 *)
(* symmx --> diagmx                                                           *)
(* unitmx --> unitarymx                                                       *)
(* normalmx --|--> unitarymx                                                  *)
(*            |--> diagmx                                                     *)
(*            |--> hermmx --> psdmx --|--> pdmx                               *)
(*                                    |--> obsmx --|--> denmx --> den1mx      *)
(*                                                 |--> projmx --> proj1mx    *)
(* den1mx --> proj1mx                                                         *)
(******************************************************************************)
(* Defining Types                                                             *)
(* 'MR[R]_(m,n) : subtype of realmx, closed under unitring                    *)
(* 'MH[R]_m     : subtype of hermmx, closed under lmod                        *)
(* 'MDen[R]_m   : subtype of denmx                                            *)
(* 'MObs[R]_m   : subtype of obsmx                                            *)
(* psdmx : closed under addr                                                  *)
(* unitarymx : closed under *m                                                *)
(******************************************************************************)
(*         vnorm R T == interface type of function f : T -> R satisfying      *)
(*                      vector norm property, over R : numDomainType          *)
(*                      and T : lmodType                                      *)
(*                      The HB class is VNorm                                 *)
(*  porderLmodType R == join of porderType and lmodType (R : ringType)        *)
(*                      The HB class is POrderedLmodule                       *)
(*      vorderType R == interface type of lmodType (R : numDomainType)        *)
(*                      equipped with a vector order                          *)
(*                      The HB class is VOrder                                *)
(******************************************************************************)
(*                             Matrix Norms                                   *)
(* -------------------------------------------------------------------------- *)
(* pnorm p : (l^(p+1) norm) (p+1).-root (\sum_(i,j) `|A i j|^+(p+1)           *)
(* schattennorm p : pnorm p over its singular values                          *)
(*                  (still lack proofs of triangle inequality)                *)
(* l1norm := pnorm 1; l2norm := pnorm 2                                       *)
(* i2norm :  induced 2-norm                                                   *)
(* fbnorm := schattennorm 2 : Frobenius norm (= l2norm)                       *)
(* trnorm := schattennorm 1 : trace/nuclear norm                              *)
(******************************************************************************)
(*                      Singular Value Decomposition (SVD)                    *)
(* let A = 'M[R]_(m,n)  R: numClosedFieldType                                 *)
(*        A = svd_u A *m cdiag_mx (svd_d A) *m (svd_v A)^*t                   *)
(*    where svd_u A and svd_v A are two square unitary matrices               *)
(*    (svd_d A) is 'rV[R]_(minn m n), with nonincreasing order of singular    *)
(*    values; cdiag_mx gives the m * n matrix with diagonal elements of D     *)
(*    (0 for extendd part, i.e., index out of minn m n)                       *)
(* let A = 'M[R]_m  R: numClosedFieldType                                     *)
(*        A = svd_u A *m diag_mx (svds_d A) *m (svd_v A)^*t                   *)
(******************************************************************************)
(* Define lowner order of matrices                                            *)
(******************************************************************************)

Ltac auto_ge0 := repeat match goal with
  | [ |- is_true (_ \is Num.nneg) ] => rewrite nnegrE
  | [ |- is_true (0 <= _ + _) ] => apply/addr_ge0
  | [ |- is_true (0 <= \sum_( _ <- _ | _ ) _ )] => apply/sumr_ge0=>? _
  | [ |- is_true (0 <= \prod_( _ <- _ | _ ) _ )] => apply/prodr_ge0=>? _
  | [ |- is_true (0 <= _ ^+ _) ] => apply/exprn_ge0
  | [ |- is_true (_.-root _ <= _.-root _) ] => rewrite ler_rootC//
  | [ |- is_true (0 <= _.-root _)] => rewrite rootC_ge0
  | [ |- is_true (0 <= _ * _)] => apply/mulr_ge0
  | [ |- is_true (0 <= `| _ |)] => apply/normr_ge0
  | [ |- _ ] => by []
end.

Section inequality.
Variable (R: numClosedFieldType).

Import Num.Syntax.

Lemma exprDnr (a b : R) (n : nat) :
  (a + b) ^+ n = \sum_(i < n.+1) ('C(n,i)%:R * (a ^+ i) * (b ^+ (n-i))).
Proof.
rewrite big_ord_rev/= exprDn; apply eq_bigr => i _.
by rewrite subSS subKn ?bin_sub// -1?ltnS// -mulr_natl mulrA.
Qed.

Lemma combination_lemma1 (k l t : nat) : 
  (\sum_(i < t.+1) (k+l) * i * 'C(k,i) * 'C(l, t-i) = k * t * 'C(k+l,t))%N.
Proof.
pose f t := (\sum_(i < t.+1) (k + l) * i * 'C(k, i) * 'C(l, t - i))%N.
suff P t' : (f t' + f t'.+1 = (k+l)*k*'C(k+l,t'))%N.
  elim: t => [|t IH]; first by rewrite /f big_ord1 ?(mul0n, muln0).
  move: (P t); rewrite /(f _) IH=>/(f_equal (subn ^~ (k * t * 'C(k + l, t))%N)).
  by rewrite -/(f _) addnC addnK [(k * t)%N]mulnC -!mulnA -mulnBl mulnCA -mul_bin_left.
transitivity (\sum_(i < t'.+1) (k + l) * (i + (k-i)) * 'C(k, i) * 'C(l, t' - i))%N.
  under eq_bigr do rewrite mulnDr mulnDl mulnDl.
  rewrite big_split/=; f_equal.
  rewrite /f big_ord_recl /=/bump/= muln0 !mul0n add0n.
  apply eq_bigr=>i _; rewrite add1n subSS; f_equal.
  by rewrite -mulnA mul_bin_left mulnA.
rewrite -[in RHS]binomial.Vandermonde big_distrr/=.
apply eq_bigr=>i _; case: (ltnP k i).
by move=>/bin_small->; rewrite ?(muln0,mul0n).
by move=>/subnKC->; rewrite !mulnA.
Qed.

Lemma combination_lemma2 (k l t : nat) : 
  (\sum_(i < t.+1) ((k+l) * (k-i) * 'C(k,i) * 'C(l, t-i))%N = k * (k+l-t) * 'C(k+l,t))%N.
Proof.
case: (ltnP (k+l) t)=>P.
  rewrite bin_small// muln0 big1// =>/= i _.
  case: (ltnP k i)=>[/bin_small->|P2]; first by rewrite muln0.
  rewrite ['C(l,_)]bin_small ?muln0//.
  by apply: (leq_trans _ (leq_sub (leqnn _) P2)); rewrite ltn_subRL.
apply/eqP; rewrite -(eqn_add2l  (k * t * 'C(k+l,t))%N) -{1}combination_lemma1.
rewrite -big_split/= -mulnDl -mulnDr subnKC// -binomial.Vandermonde big_distrr/=.
apply/eqP; apply eq_bigr=>i _; rewrite -mulnDl -mulnDl -mulnDr.
move: (leqVgt i k)=>/orP[P1|P1].
  by rewrite subnKC// [(k * _)%N]mulnC !mulnA.
by rewrite bin_small ?(muln0,mul0n).
Qed.

Lemma rootC_AGM_variant (I : finType) (a : I -> nat) (b : I -> R) :
  (forall i, 0 <= b i) ->
  (\sum_i a i)%:R * (\sum_i a i).-root (\prod_i (b i) ^+ (a i))
    <= \sum_i (a i)%:R * b i.
Proof.
move=>Pai.
have Pi : forall i, (a i)%:R * b i = \sum_(j < a i) b i.
by move=>i; rewrite sumr_const mulr_natl card_ord.
under [X in _ <= X]eq_bigr do rewrite Pi.
rewrite sig_big_dep//=.
have Pi1 : forall i, b i ^+ a i = \prod_(j < a i) b i.
by move=>i; rewrite prodr_const card_ord.
under [\prod_ _ _]eq_bigr do rewrite Pi1.
rewrite sig_big_dep//=.
have <-: #|{: {i : I & 'I_(a i)}}| = \sum_i a i.
by rewrite card_tagged sumnE/= big_map big_enum/=; 
  apply eq_bigr=>i _; rewrite card_ord.
rewrite mulrC.
case E: (#|{: {i : I & 'I_(a i)}}| == 0).
move: E=>/eqP->; rewrite mulr0 sumr_ge0//.
rewrite -ler_pdivlMr. 
by rewrite ltr0n; move: E; case: (#|{: {i : I & 'I_(a i)}}|).
by apply leif_rootC_AGM.
Qed.

Lemma eq_big_natl (a b c d : nat) (P1 P2 : pred nat) (F : nat -> R) :
  (forall i, ((a <= i < b) && P1 i) = ((c <= i < d) && P2 i))%N ->
  \sum_(a <= i < b | P1 i) F i = \sum_(c <= i < d | P2 i) F i.
Proof.
move=>P; rewrite !big_geq_mkord/=.
rewrite (big_ord_widen_cond _ (fun i => P1 i && (a <= i)%N) _ (leq_maxl b d)).
rewrite [RHS](big_ord_widen_cond _ (fun i => P2 i && (c <= i)%N) _ (leq_maxr b d)).
by apply eq_bigl=>i; rewrite -!andbA andbC P andbC.
Qed.

Lemma eq_big_nat_supp (a b : nat) (P1 P2 : pred nat) (F : nat -> R) :
  (forall i, ((i < a) && P1 i) && ~~((i < b) && P2 i) -> F i = 0%R)%N ->
  (forall i, ((i < b) && P2 i) && ~~((i < a) && P1 i) -> F i = 0%R)%N ->
  \sum_(i < a | P1 i) F i = \sum_(i < b | P2 i) F i.
Proof.
move=> Pa Pb.
rewrite (big_ord_widen_cond _ _ _ (leq_maxl a b)).
rewrite [RHS](big_ord_widen_cond _ _ _ (leq_maxr a b)).
rewrite [LHS](bigID (I :='I_(maxn a b)) (fun i => ((i < b)%N && P2 i)))/=.
rewrite [RHS](bigID (I :='I_(maxn a b)) (fun i => ((i < a)%N && P1 i)))/=.
f_equal.
by apply eq_bigl=>i; rewrite andbC [_ && P2 i]andbC [P1 i && _]andbC.
rewrite !big1// =>i; rewrite [X in X && _]andbC. apply Pa. apply Pb.
Qed.

Lemma big_ord_triangle_reindex (a b : nat) (F G : nat -> R) :
  (forall i, (a <= i)%N -> F i = 0) -> (forall i, (b <= i)%N ->  G i = 0) ->
  (\sum_(i < a) F i) * (\sum_(i < b) G i) = 
    \sum_(i < (a + b).-1) \sum_(j < i.+1) F j * G (i - j)%N.
Proof.
case: a=>[|a].
  move=>Pi _; rewrite big_ord0 mul0r big1//==>j _; 
  rewrite big1// =>i _; by rewrite Pi ?mul0r.
case: b=>[|b].
  move=>_ Pi; rewrite big_ord0 mulr0 big1//==>j _; 
  rewrite big1// =>i _; by rewrite Pi ?mulr0.
move=>PF PG.
rewrite big_distrlr addSn addnS/=.
have P1 (i : 'I_(a+b).+1) : \sum_(j < i.+1) F j * G (i - j)%N = 
    \sum_(j < a.+1 | (j <= i <= j+b)%N) F j * G (i - j)%N.
  apply: (@eq_big_nat_supp i.+1 a.+1 xpredT (fun j => (j <= i <= j+b)%N) 
    (fun j => F j * G (i - j)%N))=>j; rewrite andbT !ltnS.
  by rewrite !negb_and -leq_subLR -ltnNge=>/andP[]->/=; 
    rewrite -ltnNge=>/orP[/PF|/PG]->; rewrite ?mul0r ?mulr0.
  by rewrite -leq_subLR andbC=>/andP[]/negPf->; rewrite/= andbF.
under [RHS]eq_bigr do rewrite P1.
rewrite [RHS](exchange_big_dep xpredT)//=; apply eq_bigr=>i _.
transitivity (\sum_(0 + i <= i0 < b.+1 + i) F i * G (i0 - i)%N).
  by rewrite big_addn addnK big_mkord; under [RHS]eq_bigr do rewrite addnK.
rewrite (@eq_big_natl _ _ 0 (a+b).+1 _ (fun j=>(i <= j <= i + b)%N)) ?big_mkord// =>j.
rewrite andbT add0n leq0n/= addSn !ltnS addnC [RHS]andbC.
case: (_ <= _)%N=>//=; case E: (_ <= _)%N=>//=.
by symmetry; apply/(leq_trans E); rewrite leq_add2r -ltnS.
Qed.

Lemma discrete_Minkowski_inequality_2dim (a1 b1 a2 b2 : R) (p : nat) :
  p.-root ((`|a1| + `|b1|) ^+ p + (`|a2| + `|b2|) ^+ p) <= 
    p.-root (`|a1| ^+ p + `|a2| ^+ p) + p.-root (`|b1| ^+ p + `|b2| ^+ p).
Proof.
case: p=>[|p]; first by rewrite root0C addr0.
rewrite -[X in _ <= X](@exprCK _ p.+1)//; auto_ge0.
rewrite !exprDnr -big_split/=; apply ler_sum =>i _.
rewrite -!mulrA -mulrDr; apply ler_wpM2l=>//.
rewrite -!rootCX //; auto_ge0; rewrite -rootCMl; auto_ge0.
rewrite -[X in X <= _](@exprCK _ p.+1)//; auto_ge0.
rewrite !exprDnr -subSn; first by rewrite -ltnS.
rewrite [X in _ <= X](@big_ord_triangle_reindex _ _ 
  (fun i0 => ('C(i, i0))%:R * `|a1| ^+ p.+1 ^+ i0 * `|a2| ^+ p.+1 ^+ (i - i0))
  (fun i0 => ('C(p.+1 - i, i0))%:R * `|b1| ^+ p.+1 ^+ i0 * `|b2| ^+ p.+1 ^+ (p.+1 - i - i0))).
by move=>j /bin_small->; rewrite !mul0r.
by move=>j; rewrite subSn -1?ltnS// ltnS =>/bin_small->; rewrite !mul0r.
rewrite addSn/= subnKC; first by apply/ltnW.
apply ler_sum=>k _.
under eq_bigr do rewrite -mulrA -mulrA mulrCA !mulrA -natrM -!mulrA.
apply: (le_trans _ (rootC_AGM_variant _ _))=>[|?]; auto_ge0.
under eq_bigr do rewrite mulnC.
rewrite binomial.Vandermonde subnKC -1?ltnS//.
rewrite -mulrA; apply: ler_wpM2l=>//.
rewrite -[X in X <= _](@exprCK _ 'C(p.+1,k))//; auto_ge0.
1,2: by rewrite bin_gt0 -ltnS.
rewrite !exprMn -!exprM !mulnA mulrACA !mulrA.
under eq_bigr do rewrite !exprMn -!exprM !mulnA.
rewrite !big_split/= !prodrXr !mulrA.
(have P (a b : R) : a = b -> a <= b by move=>->); apply P.
have P1 : (p.+1 = i + (p.+1 - i))%N by rewrite subnKC// -ltnS.
do ! f_equal.
by rewrite {3}P1 -[LHS]combination_lemma1 -P1; apply eq_bigr=>j _/=; 
  rewrite -mulnA [('C(i,j) * _)%N]mulnC mulnA.
by rewrite {2 4}P1 -[LHS]combination_lemma2 -?P1 -1?ltnS//; apply eq_bigr=>j _; 
  rewrite -mulnA [('C(i,j) * _)%N]mulnC mulnA.
rewrite big_ord_rev {4}P1 addnC -[LHS]combination_lemma1;
  by apply eq_bigr=>j _/=; rewrite addnC -P1 subSS subKn// -ltnS.
rewrite {3 5}P1 addnC big_ord_rev/= -[LHS]combination_lemma2;
  by apply eq_bigr=>j _/=; rewrite addnC -P1 subSS subKn// -ltnS.
Qed.

Lemma discrete_Minkowski_inequality 
  (I : Type) (r : seq I) (P : pred I) (Fx Fy : I -> R) (p : nat) :
  p.-root (\sum_(i <- r | P i) (`|Fx i + Fy i|) ^+ p) <=
    p.-root (\sum_(i <- r | P i) (`|Fx i|) ^+ p) + 
    p.-root (\sum_(i <- r | P i) (`|Fy i|) ^+ p).
Proof.
case: p=>[|p]; first by rewrite root0C addr0.
elim: r; first by rewrite !big_nil rootC0 addr0.
move=>i l IH; rewrite !big_cons; case E: (P i)=>//.
set a1 := Fx i. set b1 := Fy i.
set a2 := p.+1.-root (\sum_(j <- l | P j) normr (Fx j) ^+ p.+1) in IH.
set b2 := p.+1.-root (\sum_(j <- l | P j) normr (Fy j) ^+ p.+1) in IH.
move: (discrete_Minkowski_inequality_2dim a1 b1 a2 b2 p.+1).
suff ->: normr a2 ^+ p.+1 = \sum_(j <- l | P j) normr (Fx j) ^+ p.+1.
suff ->: normr b2 ^+ p.+1 = \sum_(j <- l | P j) normr (Fy j) ^+ p.+1.
apply le_trans; rewrite ler_rootC //; auto_ge0.
apply lerD; first by apply lerXn2r; auto_ge0; apply: ler_normD.
rewrite -(@ler_rootC _ p.+1)//; [auto_ge0 ..|].
apply (le_trans IH); rewrite exprCK//; auto_ge0.
apply lerD; rewrite ger0_norm// /a2 /b2; auto_ge0.
all: by rewrite norm_rootC rootCK// ger0_norm//; auto_ge0.
Qed.

Lemma Cauchy_Schwarz_C I (r: seq I) (P: pred I) (X Y : I -> R) :
  (\sum_(i <- r | P i) `|X i|^+2) * (\sum_(i <- r | P i) `|Y i|^+2) 
    >= `| \sum_(i <- r | P i) X i * Y i|^+2.
Proof.
move: (discrete_Minkowski_inequality r P (fun i => `|X i|) (fun i => `|Y i|) 2).
have ->: \sum_(i <- r | P i) `| `|X i| + `|Y i| | ^+ 2 = 
  \sum_(i <- r | P i) (`|X i| ^+ 2 + 2%R * (`|X i| * `|Y i|) + `|Y i| ^+ 2).
by apply eq_bigr=>i _; rewrite mulr_natl -sqrrD ger0_norm; auto_ge0.
under [in X in _ <= X + _]eq_bigr do rewrite normrE.
under [in X in _ <= _ + X]eq_bigr do rewrite normrE.
move=>/(lerXn2r 2). rewrite sqrrD !sqrtCK -sqrtCM; auto_ge0.
rewrite {2}big_split/= lerD2r [X in _ -> _ -> X <= _]big_split/= lerD2l.
rewrite -mulr_sumr mulr_natl ler_pMn2r// =>P1.
rewrite -(@ler_rootC _ 2)//; [auto_ge0..|].
apply: (le_trans _ (P1 _ _)); auto_ge0.
rewrite exprCK//. apply/(le_trans (ler_norm_sum _ _ _)).
by apply ler_sum=>i _; rewrite normrM.
Qed.

Lemma normr_sqr_ler_sum (I : finType) (P: pred I) (X : I -> R) :
  (\sum_(i | P i) `|X i|^+2) <= (\sum_(i | P i) `|X i|)^+2.
Proof.
rewrite expr2 big_distrlr/= ler_sum// =>i Pi.
by rewrite (bigD1 i)//= -expr2 ler_wpDr// sumr_ge0// =>j _; rewrite mulr_ge0.
Qed.

End inequality.


(* -------------------------------------------------------------------- *)
(* definition of qualifiers *)

Section TrivialMatrix.
Variable (R: ringType).

Lemma mx_dim0n p : all_equal_to (0 : 'M[R]_(0,p)).
Proof. by move=>x/=; apply/matrixP=>i j; destruct i. Qed.
Lemma mx_dimn0 p : all_equal_to (0 : 'M[R]_(p,0)).
Proof. by move=>x/=; apply/matrixP=>i j; destruct j. Qed.
Definition mx_dim0E := (mx_dim0n,mx_dimn0).
(* Lemma mxf_dim0n T p : all_equal_to ((fun=>0) : T -> 'M[R]_(0,p)).
Proof. by move=>h/=; apply/funext=>i; rewrite mx_dim0E. Qed.
Lemma mxf_dimn0 T p : all_equal_to ((fun=>0) : T -> 'M[R]_(p,0)).
Proof. by move=>h/=; apply/funext=>i; rewrite mx_dim0E. Qed.
Definition mxf_dim0E := (mxf_dim0n,mxf_dimn0).

Definition mx_dim0 := (mx_dim0n,mx_dimn0,mxf_dim0n,mxf_dimn0). *)

End TrivialMatrix.

Lemma big_card0 (T : Type) (idx : T) (op : T -> T -> T) (I : finType) 
  (r: seq I) (P : pred I) 
  (F: I -> T): #|I| = 0%N ->
  \big[op/idx]_(i <- r | P i) F i = idx.
Proof.
elim: r. by rewrite big_nil.
move=>a l _ PI. exfalso. move: (fintype0 a)=>//.
Qed.

Lemma index_enum1 (I : finType) i0 :
  #|I| = 1%N -> index_enum I = [:: i0].
Proof.
move=>Pi. move: Pi {+}Pi=>/mem_card1[x Px] /eqP/fintype1P[y Py].
by rewrite/index_enum/= -fintype.enumT (fintype.eq_enum Px) fintype.enum1 !Py.
Qed.

Lemma big_card1E T (idx : T) (op : T -> T -> T) (I : finType) i0 (F : I -> T) :
  #|I| = 1%N -> \big[op/idx]_i F i = op (F i0) idx.
Proof. by move=>P1; rewrite unlock/= (index_enum1 i0). Qed.
Arguments big_card1E [T idx op I] i0 [F].

Lemma big_card1 T (idx : T) (op : Monoid.law idx) (I : finType) i0 (F : I -> T) :
  #|I| = 1%N -> \big[op/idx]_i F i = F i0.
Proof.
move=>Pi. suff: (fun=>true) =1 pred1 i0. by apply big_pred1.
by move=>i; rewrite/=; move/eqP/fintype1P: Pi=>[x Px]; rewrite !Px eqxx.
Qed.
Arguments big_card1 [T idx op I] i0 [F].

Lemma mulmxACA (R: ringType) m1 m2 m3 m4 m5 
 (M1 :'M[R]_(m1,m2)) (M2 : 'M_(m2,m3)) (M3 : 'M_(m3,m4)) (M4 : 'M_(m4,m5)) :
  M1 *m M2 *m M3 *m M4 = M1 *m (M2 *m M3) *m M4.
Proof. by rewrite !mulmxA. Qed.

Lemma delta_mx_mulEl (R: ringType) {m n l} (A : 'M[R]_(m , n)) i (j:'I_l) p q :
  (A *m delta_mx i j) p q = (j == q)%:R * A p i.
Proof.
rewrite mxE (bigD1 i)// big1/= ?mxE ?eqxx/= ?addr0 1?eq_sym 1?mulrC//.
move=>k /negPf Pk; rewrite mxE Pk/= mulr0//.
by case: eqP=> _; rewrite ?mulr1 ?mul1r ?mul0r ?mulr0.
Qed.

Lemma delta_mx_mulEr (R: ringType) {m n l} (A : 'M[R]_(m , n)) (i:'I_l) j p q :
  (delta_mx i j *m A) p q = (i == p)%:R * A j q.
Proof.
rewrite mxE (bigD1 j)// big1/= ?mxE ?eqxx/= ?addr0 1?eq_sym ?andbT//.
move=>k /negPf Pk; rewrite mxE Pk/= andbF mul0r//.
Qed.

Section ConjAdjmx.
Variable (R : numClosedFieldType) (m n : nat).

Definition conjmx (M : 'M[R]_(m,n)) := 
    (map_mx Num.conj_op M).

Definition adjmx (M : 'M[R]_(m,n)) := 
    (map_mx Num.conj_op (M ^T)).

Lemma conjmxE M : conjmx M = (map_mx Num.conj_op M).
Proof. by []. Qed.
Lemma adjmxE M : adjmx M = (map_mx Num.conj_op (M ^T)).
Proof. by []. Qed.

Lemma mxE_conj M i j : conjmx M i j = (M i j)^*.
Proof. by rewrite mxE. Qed.

Lemma mxE_adj M i j : adjmx M i j = (M j i)^*.
Proof. by rewrite !mxE. Qed.

End ConjAdjmx.

Notation "M ^*m" := (conjmx M).
Notation "M ^*t" := (adjmx M).

Section ConjAdjmxTheory.
Variable (R : numClosedFieldType).

Lemma conjmx_is_antilinear {m n} :
  linear_for (Num.conj_op \; *:%R) (@conjmx R m n).
Proof. 
move=>a A B. apply/matrixP=>i j.
by rewrite !mxE raddfD/= rmorphM.
Qed.

HB.instance Definition _ m n :=
  GRing.isLinear.Build R 'M_(m, n) 'M_(m, n)
    (Num.conj_op \; *:%R) (@conjmx R m n) (@conjmx_is_antilinear m n).

Lemma conjmx_is_multiplicative {m } : multiplicative (@conjmx R m.+1 m.+1).
Proof. split.
- move=> A B; apply/matrixP=> i j; rewrite !mxE rmorph_sum.
  by apply: eq_bigr=> /= k _; rewrite rmorphM /= !mxE.
- by apply/matrixP=> i j; rewrite !mxE conjC_nat.
Qed.

HB.instance Definition _ m :=
  GRing.isMultiplicative.Build 'M_m.+2 'M_m.+2
    (@conjmx R m.+2 m.+2) (@conjmx_is_multiplicative m.+1).

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
rewrite rmorphM rmorphXn /= rmorphN conjC1; congr (_ * _).
by rewrite rmorph_prod; apply: eq_bigr=> /= i _; rewrite mxE.
Qed.

Lemma conjmx_scale m (a : R) : (a%:M : 'M[R]_m)^*m = (a^*)%:M.
Proof. by apply/matrixP=>i j; rewrite !mxE rmorphMn. Qed.

Lemma conjmx1 m : (1%:M : 'M[R]_m)^*m = 1%:M.
Proof. by rewrite conjmx_scale conjC1. Qed.

(* ==================================================================== *)

Lemma adjmxTC {m n : nat} (M : 'M[R]_(m, n)) : M^*t = M^T^*m.
Proof. by []. Qed.

Lemma adjmxCT {m n : nat} (M : 'M[R]_(m, n)) : M^*t = M^*m^T.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma adjmx_is_antilinear {m n} : linear_for (Num.conj_op \; *:%R) (@adjmx R m n).
Proof. by move=>a A B; rewrite !adjmxCT linearP/= linearP/=. Qed.

HB.instance Definition _ m n :=
  GRing.isLinear.Build R 'M_(m, n) 'M_(n, m)
    (Num.conj_op \; *:%R) (@adjmx R m n) (@adjmx_is_antilinear m n).

Lemma adjmxD {m n} (A B: 'M[R]_(m, n)) : (A + B)^*t = A^*t + B^*t.
Proof. exact: linearD. Qed.

Lemma adjmxZ {m n} (c: R) (A : 'M[R]_(m, n)) : (c *: A)^*t = c^* *: A^*t.
Proof. exact: linearZ. Qed.

Lemma adjmxP {m n} (c: R) (A B: 'M[R]_(m, n)) : 
  (c *: A + B)^*t = c^* *: A^*t + B^*t.
Proof. exact: linearP. Qed.

Lemma adjmxM {m n p} (A: 'M[R]_(m, n)) (B: 'M[R]_(n, p)) :
  (A *m B)^*t = B^*t *m A^*t.
Proof. by rewrite !adjmxCT conjmxM trmx_mul. Qed.

Lemma adjmxK {m n : nat} : cancel (@adjmx R m n) (@adjmx R n m).
Proof. by move=> M; rewrite adjmxCT adjmxTC conjmxK trmxK. Qed.

Lemma adjmx_inj {m n} : injective (@adjmx R m n).
Proof. by move=> M N P; rewrite -(adjmxK M) -(adjmxK N) P. Qed.

Lemma adjmx_eq0  m n (A : 'M[R]_(m, n)) : (A^*t == 0) = (A == 0).
Proof. by apply raddf_eq0; apply adjmx_inj. Qed.

Lemma det_adj {m : nat} (M : 'M[R]_m) : \det M^*t = (\det M)^*.
Proof. by rewrite adjmxCT det_tr det_conj. Qed.

Lemma adjmx_scale m (a : R) : (a%:M : 'M[R]_m)^*t = (a^*)%:M.
Proof. by apply/matrixP=>i j; rewrite !mxE rmorphMn eq_sym. Qed.

Lemma adjmx1 m : (1%:M : 'M[R]_m)^*t = 1%:M.
Proof. by rewrite adjmx_scale conjC1. Qed.

Lemma conjmx_delta m n (i : 'I_m) (j : 'I_n) : 
  (@delta_mx R _ _ i j)^*m = delta_mx i j.
Proof. by apply/matrixP=>a b; rewrite !mxE conjC_nat. Qed.

Lemma adjmx_delta m n (i : 'I_m) (j : 'I_n) : 
  (@delta_mx R _ _ i j)^*t = delta_mx j i.
Proof. by apply/matrixP=>a b; rewrite !mxE conjC_nat andbC. Qed.

(* between adjmx conjmx trmx *)
Lemma trmxCA {m n : nat} (M : 'M[R]_(m, n)) : M^T = M^*m^*t.
Proof. by rewrite adjmxCT conjmxK. Qed.

Lemma trmxAC {m n : nat} (M : 'M[R]_(m, n)) : M^T = M^*t^*m.
Proof. by rewrite adjmxTC conjmxK. Qed.

Lemma conjmxAT {m n : nat} (M : 'M[R]_(m, n)) : M^*m = M^*t^T.
Proof. by rewrite trmxAC adjmxK. Qed.

Lemma conjmxTA {m n : nat} (M : 'M[R]_(m, n)) : M^*m = M^T^*t.
Proof. by rewrite trmxCA adjmxK. Qed.

Lemma mxCAC {m n : nat} (M : 'M[R]_(m, n)) : M^*m^*t = M^*t^*m.
Proof. by rewrite -trmxCA -trmxAC. Qed.

Lemma mxACC {m n : nat} (M : 'M[R]_(m, n)) : M^*t^*m = M^*m^*t.
Proof. by rewrite -trmxCA -trmxAC. Qed.

Lemma mxATC {m n : nat} (M : 'M[R]_(m, n)) : M^*t^T = M^T^*t.
Proof. by rewrite -conjmxAT -conjmxTA. Qed.

Lemma mxTAC {m n : nat} (M : 'M[R]_(m, n)) : M^T^*t = M^*t^T.
Proof. by rewrite -conjmxAT -conjmxTA. Qed.

Lemma mxCTC {m n : nat} (M : 'M[R]_(m, n)) : M^*m^T = M^T^*m.
Proof. by rewrite -adjmxCT -adjmxTC. Qed.

Lemma mxTCC {m n : nat} (M : 'M[R]_(m, n)) : M^T^*m = M^*m^T.
Proof. by rewrite -adjmxCT -adjmxTC. Qed.

Lemma mxtrace_adj {m : nat} (M : 'M[R]_m) : \tr M^*t = (\tr M)^*.
Proof. by rewrite -[in RHS]mxtrace_tr -trace_map_mx -adjmxE. Qed.

Lemma mxtrace_conj {m : nat} (M : 'M[R]_m) : \tr M^*m = (\tr M)^*.
Proof. by rewrite -trace_map_mx. Qed.

Lemma adj_row {m n : nat} (M : 'M[R]_(m, n)) i :
  (row i M)^*t = col i M^*t.
Proof. by rewrite adjmxE tr_row map_col. Qed.

Lemma adj_col {m n : nat} (M : 'M[R]_(m, n)) i :
  (col i M)^*t = row i M^*t.
Proof. by rewrite adjmxE tr_col map_row. Qed. 

Lemma mxrank_adj {m n : nat} (M : 'M[R]_(m, n)) :
  \rank M^*t = \rank M.
Proof. by rewrite mxrank_map mxrank_tr. Qed.

End ConjAdjmxTheory.

Section MxCast.
Variable (R: numClosedFieldType).

Lemma adjmx_castV m n m' n' (eqS: (n = n') * (m = m')) 
(A: 'M[R]_(m,n)) : castmx eqS (A^*t) = (castmx (eqS.2,eqS.1) A)^*t.
Proof. by rewrite castmx_funE. Qed.

Lemma trmx_castV m n m' n' (eqS: (n = n') * (m = m')) 
(A: 'M[R]_(m,n)) : castmx eqS (A^T) = (castmx (eqS.2,eqS.1) A)^T.
Proof. by rewrite castmx_funE. Qed.

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

Section EigenDecomposition.
Variable (C : numClosedFieldType) (n : nat).
Implicit Type (A : 'M[C]_n).

Definition eigenmx A : 'M[C]_n := (spectralmx A)^*t.
Definition eigenval A i :=  spectral_diag A 0 i.
Definition eigenvec A i :=  col i (eigenmx A).

Lemma eigenvec_ortho A i j :
  ((eigenvec A i)^*t *m (eigenvec A j))= (i == j)%:R%:M.
Proof.
apply/matrixP=>k l; rewrite !ord1 /eigenvec adj_col -mulmx_rowcol /eigenmx adjmxK.
move/unitarymxP: (spectral_unitarymx A)=>->. by rewrite !mxE.
Qed.

Lemma eigen_unitarymx A : eigenmx A \is unitarymx.
Proof. rewrite trmxC_unitary; exact: spectral_unitarymx. Qed.

Lemma eigen_unitmx  A : eigenmx A \in unitmx.
Proof. apply/unitarymx_unit/eigen_unitarymx. Qed.

Lemma eigen_dec A :
  let P := eigenmx A in let sp := spectral_diag A in
    reflect (A = P *m diag_mx sp *m P ^*t) (A \is normalmx).
Proof. 
rewrite/= /eigenmx adjmxK adjmxE; apply (iffP idP);
  move/invmx_unitary: (spectral_unitarymx A)=><-.
apply/orthomx_spectralP. by move/orthomx_spectralP.
Qed.

Lemma eigen_sum A :
  reflect (A = \sum_i eigenval A i *: ((eigenvec A i) *m (eigenvec A i)^*t))
    (A \is normalmx).
Proof.
apply/(iffP (eigen_dec A))=>{1}->; [symmetry|]; apply/matrixP=>i j.
all: rewrite mul_mx_diag mulmx_rowcol mxE summxE; apply eq_bigr=>k _; 
  by rewrite !mxE big_ord1 !mxE mulrA [eigenval _ _ * _]mulrC.
Qed.

Lemma eigenmx_eigenvec A i :
  A \is normalmx ->
  A *m (eigenvec A i) = eigenval A i *: (eigenvec A i).
Proof.
move=>/eigen_sum{1}->; rewrite mulmx_suml (bigD1 i)//= big1=>[j /negPf nji|];
by rewrite scalemxAl -mulmxA eigenvec_ortho ?nji ?scalemx0 ?mulmx0// eqxx mulmx1 addr0.
Qed.

End EigenDecomposition.

Global Hint Resolve spectral_unitarymx : core.
Global Hint Resolve eigen_unitarymx : core.

(* -------------------------------------------------------------------- *)

Section SPredMxDef.
Context {R : numClosedFieldType} (n : nat).

Definition hermmx := (@sesqui R n (false, Num.conj_op)).
Fact hermmx_key : pred_key hermmx. Proof. by []. Qed.
Canonical hermmx_keyed := KeyedQualifier hermmx_key.

Lemma hermmxP (A : 'M[R]_n) :
  reflect (A = A^*t) (A \is hermmx).
Proof. 
apply (iffP (sesquiP _ _ A)); by rewrite expr0 scale1r.
Qed.

Definition symmx := (@sesqui R n (false, (GRing.RMorphism.clone _ _ idfun _))).
Fact symmx_key : pred_key symmx. Proof. by []. Qed.
Canonical symmx_keyed := KeyedQualifier symmx_key.

Lemma symmxP (A : 'M[R]_n) :
  reflect (A = A^T) (A \is symmx).
Proof. 
by apply (iffP (sesquiP _ _ A)); rewrite expr0 scale1r map_mx_id.
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
  reflect ((A \is hermitian) /\ ((spectral_diag A) \is a nnegmx)) (A \is psdmx).
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

HB.instance Definition _ := GRing.isAddClosed.Build
  ('M[R]_(m, n)) (@realmx R m n) realmx_zmod_closed.
HB.instance Definition _ := GRing.isOppClosed.Build
  ('M[R]_(m, n)) (@realmx R m n) realmx_zmod_closed.
HB.instance Definition _ := GRing.isAddClosed.Build
  ('M[R]_(m, n)) (@nnegmx R m n) nnegmx_addr_closed.

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

HB.instance Definition _ := GRing.isMulClosed.Build 
  ('M[R]_(m.+1, m.+1)) (@realmx R m.+1 m.+1) realmx_divring_closed.
HB.instance Definition _ := GRing.isInvClosed.Build 
  ('M[R]_(m.+1, m.+1)) (@realmx R m.+1 m.+1) realmx_divring_closed.

End RealMxDivRingClosed.


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
Proof. by move/eigen_dec=>{1}->; rewrite -mulmxA mxtrace_mulC mulmxKtV. Qed.

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
move=>/eigen_dec {1}->.  
rewrite mxrankMfree; last rewrite -mxrank_tr trmx_mul mxrankMfree.
1,2: apply/eqP; rewrite ?mxrank_tr; apply mxrank_unitary; rewrite ?trmxC_unitary//.
by rewrite mxrank_tr.
Qed.

Lemma rank11 (N : 'M[R]_1) : \rank N = (N 0 0 != 0).
Proof.
rewrite rank_rV; case: eqP=>[->|]; case: eqP=>//. by rewrite mxE.
move=>P1 P2; exfalso; apply P2; apply/matrixP=>i j; by rewrite !mxE !ord1.
Qed.

Lemma rank_diagmx n (N: 'rV[R]_n) :
  \rank (diag_mx N) = (\sum_i (N 0 i != 0)%R)%N.
Proof.
elim/row_ind : N =>[N|p x N IH]; first by rewrite mxrank.unlock unlock /= big_ord0.
rewrite diag_mx_row rank_diag_block_mx big_split_ord/= big_ord1; do 2 f_equal.
by rewrite rank11 !mxE; case: fintype.splitP=>j// _; rewrite ord1 eqxx mulr1n.
rewrite IH; apply eq_bigr=>i _; rewrite mxE; case: fintype.splitP=>//= j.
by move=>P1; exfalso; move: P1; destruct j=>/= P1; move: i0; rewrite -P1.
by rewrite !add1n=>/eq_add_S/ord_inj->.
Qed.

Lemma sum_nat_eq1 (I : finType) (F : I -> nat) :
  (\sum_i F i = 1)%N -> exists i, forall j, F j = (i == j).
Proof.
move=>P1; have: exists i, (F i != 0)%N.
  apply/existsP; rewrite -negb_forall. apply/negP=>/forallP=>P2.
  by move: P1; rewrite big1=>//i _; move/eqP: (P2 i).
move=>[i Pi]; exists i=> j.
have addn_eq1 a b : (a + b = 1 -> (a = 1 /\ b = 0) \/ (a = 0 /\ b = 1))%N.
case: a; case b=>//=.
1,2: move=>n; rewrite ?addn0 ?add0n; case: n=>//; by [right| left].
by move=>n n'; rewrite addSn addnS.
have P3: (F i = 1)%N by move: P1 Pi; rewrite (bigD1 i)//==>/addn_eq1=>[[[//]|[->]]].
case: eqP=>[ <-//|/eqP/negPf P2]/=.
move: P1; rewrite (bigD1 i)//= P3 addSn=>/eq_add_S.
rewrite add0n=>/eqP; rewrite sum_nat_eq0=>/forallP/(_ j).
by rewrite eq_sym P2/==>/eqP.
Qed.

Lemma proj1mx_diagP M : M \is proj1mx -> 
  exists i, spectral_diag M = delta_mx 0 i.
Proof.
move/proj1mxP=>[/projmxP[/hermmx_normal/normalmx_rank->]/boolmxP /(_ 0)P1 /eqP].
rewrite rank_diagmx=>/sum_nat_eq1[i P]; exists i.
apply/matrixP=>x y; rewrite !mxE !ord1 eqxx/=; case: eqP=>[->|/eqP/negPf P2].
by move: (P i) (P1 i); rewrite eqxx/=; case: eqP=>//= _ _ /eqP->.
by move: (P y); rewrite [i == _]eq_sym P2; case: eqP.
Qed.

Lemma proj1mx_den1 M : M \is proj1mx -> M \is den1mx.
Proof.
move=> P; move: {+}P=>/proj1mx_proj/projmx_obs/obsmx_psd=>P1.
apply/den1mxP; split=>//; rewrite trace_spectral_diag.
by move: P1=>/psdmx_herm/hermmx_normal.
by move: P=>/proj1mx_diagP [x H]; rewrite H mxtrace_diag (bigD1 x)// big1/=
  =>[j /negPf njx|]; rewrite mxE ?njx ?andbF// !eqxx addr0.
Qed.

End MxPredElement.
End MxPredHierarchy.

Section ExtraTheory.
Variable (R: numClosedFieldType).

Lemma mx_dot_diag n (M: 'M[R]_n) (u: 'cV[R]_n) : 
  M \is diagmx -> \tr (u^*t *m M *m u) = \sum_i M i i * `|u i 0| ^+2.
Proof.
move/diagmxP=>Pm; rewrite trace_mx11 mxE; apply eq_bigr=>i _.
rewrite !mxE (bigD1 i)// big1/==>[j nji|]; first by rewrite Pm// mulr0.
by rewrite addr0 !mxE normCK mulrA [RHS]mulrC mulrA.
Qed.

Lemma mx_dot_diag_mx n M (u: 'cV[R]_n) : 
  \tr (u^*t *m diag_mx M *m u) = \sum_i M 0 i * `|u i 0| ^+2.
Proof.
move: (diag_mx_is_diag M)=>/mx_dot_diag P; rewrite (P u).
by under eq_bigr do rewrite mxE eqxx mulr1n.
Qed.

Lemma mx_dot_eq0 n (M: 'M[R]_n)  : 
  reflect (forall (u: 'cV[R]_n), \tr (u^*t *m M *m u) = 0) (M == 0).
Proof.
apply (iffP eqP).
by move=>-> u; rewrite mulmx0 mul0mx linear0.
move=>P. apply/matrixP=>i j. rewrite mxE.
move: (P (delta_mx i 0)) (P (delta_mx j 0)) (P (delta_mx j 0 + delta_mx i 0))
(P ('i *: (delta_mx j 0) + delta_mx i 0)).
rewrite !linearD/= !mulmxDl !linearD/= !linearZ/= !linearZl_LR /= !linearZ/==>->->.
rewrite !mulr0 !addr0 !add0r conjCi mulNr.
move/addr0_eq=> <-. rewrite mulrN opprK -mulrDl trace_mx11 !mxE.
rewrite (bigD1 j)//= big1.
by move=>k /negPf nkj; rewrite !mxE nkj mulr0.
rewrite !mxE (bigD1 i)//= big1.
by move=>k /negPf nki; rewrite !mxE nki conjC0 mul0r.
rewrite !mxE !eqxx conjC1 mulr1 mul1r !addr0 mulrC.
move/eqP. rewrite mulIr_eq0. apply/rregP.
by rewrite -mulr2n mulrn_eq0 negb_or/= neq0Ci.
by move/eqP.
Qed.

Lemma hermmx_dot n (M: 'M[R]_n) :
  reflect (forall u: 'cV[R]_n, \tr (u^*t *m M *m u) \is Num.real) (M \is hermmx).
Proof.
apply (iffP (sesquiP _ _ M)); rewrite expr0 scale1r -adjmxE.
by move=> H u; apply/CrealP; rewrite/= -mxtrace_adj !adjmxM adjmxK mulmxA -H.
move=> H; apply/subr0_eq/eqP/mx_dot_eq0=>u.
rewrite mulmxDr mulmxDl linearD/= mulmxN mulNmx linearN/=.
by move: (H u)=>/CrealP<-; rewrite -mxtrace_adj !adjmxM adjmxK mulmxA addrN.
Qed.

Lemma psdmx_dot n (M: 'M[R]_n)  : 
  reflect (forall u: 'cV[R]_n, \tr (u^*t *m M *m u) \is Num.nneg) (M \is psdmx).
Proof.
apply (iffP (psdmxP M))=>[[Pm Pd] u | P].
move/eigen_dec: (hermitian_normalmx Pm)=>->.
move: (mx_dot_diag_mx (spectral_diag M) ((eigenmx M)^*t *m u)).
rewrite !adjmxM !mulmxA !nnegrE adjmxK=>->.
apply sumr_ge0=> i _; apply mulr_ge0.
  rewrite -nnegrE; move/nnegmxP: Pd=>Pd; apply Pd.
  apply exprn_ge0; apply normr_ge0.
have Pm: M \is hermmx. 
by apply/hermmx_dot=>u; move: (P u); by rewrite nnegrE realE=>->.
split=>//; move/eigen_dec: (hermitian_normalmx Pm) => P1.
apply/nnegmxP=>i j; rewrite ord1.
move: (P ((spectralmx M)^*t *m delta_mx j 0)).
rewrite {2}P1 !adjmxM !mulmxA adjmxK !mulmxtVK//.
rewrite mx_dot_diag_mx (bigD1 j)// big1/=.
  by move=>k /negPf nkj; rewrite !mxE nkj normrE expr0n mulr0.
  by rewrite !mxE !eqxx normrE expr1n mulr1 addr0.
Qed.

Lemma psdmx_bimap_closed_gen n (M: 'M[R]_n) m (A: 'M[R]_(m,n)) : 
  M \is psdmx -> A *m M *m A ^*t \is psdmx.
Proof.
move/psdmx_dot=>P; apply/psdmx_dot=>u.
by move: (P (A^*t *m u)); rewrite adjmxM !mulmxA adjmxK.
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
move/diagmx_nnegmx_psd/(psdmx_bimap_closed_gen (eigenmx M)).
rewrite !linearB/= mulmxBl diag_const_mx mulmx1.
move: (eigen_unitarymx M)=>/unitarymxP=>->.
by move: (hermitian_normalmx Pm)=>/eigen_dec <-.
move/andP=>[/psdmxP [P1 P2] /psdmx_dot P3].
apply/obsmxP. split=>//.
apply/uintmxP=>i j. apply/andP. split. by apply/nnegmxP.
move: (P3 (eigenmx M *m delta_mx j i)).
move: (hermitian_normalmx P1)=>/eigen_dec P4.
rewrite {2}P4 !linearB/= mulmxBl linearB/= !adjmxM !mulmxA mulmx1 
  !mulmxKtV// mx_dot_diag_mx (bigD1 j)// big1/=.
by move=>k /negPf nkj; rewrite !mxE nkj normrE expr0n mulr0.
rewrite trace_mx11 mxE (bigD1 j)// big1/=.
by move=>k /negPf nkj; rewrite !mxE nkj mulr0.
rewrite !mxE ord1 !eqxx/= conjC1 mulr1 normrE expr1n mulr1 !addr0.
by rewrite nnegrE subr_ge0.
Qed.

Lemma obsmx_dot n (M: 'M[R]_n) : 
  reflect (forall u: 'cV[R]_n, 0 <= \tr (u^*t *m M *m u) <= \tr (u^*t *m u)) (M \is obsmx).
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

Lemma psdmx_tr (n : nat) (A : 'M[R]_n) :
  A^T \is psdmx = (A \is psdmx).
Proof.
suff P : forall (B : 'M[R]_n), B \is psdmx -> B^T \is psdmx.
case E: (A \is psdmx). by apply P. move: E. apply contraFF=>/P. by rewrite trmxK.
move=>B /psdmx_dot P. apply/psdmx_dot=>u. move: (P (map_mx Num.conj_op u)).
by rewrite -mxtrace_tr !trmx_mul !map_trmx trmxK map_mxCK mulmxA.
Qed.

Lemma obsmx_tr (n : nat) (A : 'M[R]_n) :
  A^T \is obsmx = (A \is obsmx).
Proof.
by rewrite !obsmx_psd_eq psdmx_tr; congr (_ && _); 
  rewrite -psdmx_tr linearB/= trmx1 trmxK.
Qed.

Lemma denmx_tr (n : nat) (A : 'M[R]_n) :
  A^T \is denmx = (A \is denmx).
Proof. by rewrite qualifE [RHS]qualifE psdmx_tr mxtrace_tr. Qed.

Lemma psdmx_adj (n : nat) (A : 'M[R]_n) :
  A^*t \is psdmx = (A \is psdmx).
Proof.
suff P : forall (B : 'M[R]_n), B \is psdmx -> B^*t \is psdmx.
case E: (A \is psdmx); by [apply P | move: E; apply contraFF=>/P; rewrite adjmxK].
move=>B /psdmx_dot P. apply/psdmx_dot=>u.
by rewrite -{2}[u]adjmxK -!adjmxM mxtrace_adj nnegrE conjC_ge0 -nnegrE mulmxA.
Qed.

Lemma obsmx_adj (n : nat) (A : 'M[R]_n) :
  A^*t \is obsmx = (A \is obsmx).
Proof.
by rewrite !obsmx_psd_eq psdmx_adj; congr (_ && _); 
  rewrite -psdmx_adj linearB/= adjmx1 adjmxK.
Qed.

Lemma denmx_adj (n : nat) (A : 'M[R]_n) :
  A^*t \is denmx = (A \is denmx).
Proof.
rewrite qualifE [RHS]qualifE psdmx_adj mxtrace_adj .
by rewrite -subr_ge0 -conjC_ge0 rmorphB conjC1 conjCK subr_ge0.
Qed.

Lemma psdmx_conj (n : nat) (A : 'M[R]_n) :
  A^*m \is psdmx = (A \is psdmx).
Proof. by rewrite conjmxAT psdmx_tr psdmx_adj. Qed.

Lemma obsmx_conj (n : nat) (A : 'M[R]_n) :
  A^*m \is obsmx = (A \is obsmx).
Proof. by rewrite conjmxAT obsmx_tr obsmx_adj. Qed.

Lemma denmx_conj (n : nat) (A : 'M[R]_n) :
  A^*m \is denmx = (A \is denmx).
Proof. by rewrite conjmxAT denmx_tr denmx_adj. Qed.

End ExtraTheory.

Lemma mxtraceE {R: ringType} n (A : 'M[R]_n) :
  \tr A = \sum_i A i i.
Proof. by []. Qed.

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

HB.instance Definition _ := GRing.isAddClosed.Build
  'M_m (@hermmx R m) hermmx_zmod_closed.
HB.instance Definition _ := GRing.isOppClosed.Build
  'M_m (@hermmx R m) hermmx_zmod_closed.

Lemma psdmx_add: operator_closed (@psdmx R m) (+%R).
Proof. 
move=> A B /psdmx_dot hA /psdmx_dot hB. apply/psdmx_dot=>u.
move: (hA u) (hB u). rewrite mulmxDr mulmxDl linearD/= !nnegrE.
by apply ler_wpDl.
Qed.

Fact psdmx_addr_closed : addr_closed (@psdmx R m).
Proof. split. apply psdmx0. apply psdmx_add. Qed.

HB.instance Definition _ := GRing.isAddClosed.Build
  'M_m (@psdmx R m) psdmx_addr_closed.

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
apply/hermmx_dot=>u. move: (Pb (A^*t *m u)).
by rewrite adjmxM adjmxK !mulmxA.
Qed.

Fact psdmx_bimap_closed : bimap_closed (@psdmx R m).
Proof.
move=>A B _ /psdmx_dot Pb.
apply/psdmx_dot=>u. move: (Pb (A^*t *m u)).
by rewrite adjmxM adjmxK !mulmxA.
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
move: (hB (A^*t *m u)).
by rewrite adjmxM -!mulmxA adjmxK [A *m (A ^*t *m _)]mulmxA hA mul1mx.
Qed.

End ExtraMxPredClosed.

(* -------------------------------------------------------------------- *)
Section RealMxType.
Context {R : numDomainType} (m n : nat).

Variant realmx_t :=
  RealMx (M : 'M[R]_(m, n)) of M \is a realmx.

Coercion realmx_mx (M : realmx_t) :=
  let: RealMx M _ := M in M.

Definition realmx_isSub := Eval hnf in [isSub for realmx_mx].
HB.instance Definition _ := realmx_isSub.
HB.instance Definition _ := [Choice of realmx_t by <:].

Lemma realmx_inj : injective realmx_mx. Proof. exact: val_inj. Qed.

(* Definition realmx_of of phant R := realmx_t.
Identity Coercion type_realmx_of : realmx_of >-> realmx_t. *)
End RealMxType.

(* Bind Scope ring_scope with realmx_of. *)
Bind Scope ring_scope with realmx_t.

Arguments realmx_mx {R m n} M%R.
Arguments realmx_inj {R m n} [A%R B%R] : rename.

Notation "''MR[' R ]_ ( m , n )" := (@realmx_t R m n)
  (at level 8, format "''MR[' R ]_ ( m , n )").

(* -------------------------------------------------------------------- *)
Section RealMxOf.
Context {R : numDomainType} (m n : nat).

HB.instance Definition _ := [Choice of 'MR[R]_(m, n) by <:].

End RealMxOf.

(* -------------------------------------------------------------------- *)
Section RealMxZmod.
Context {R : numDomainType} (m n : nat).
(*
Definition realmx_zmodMixin := [zmodMixin of 'MR[R]_(m, n) by <:].
Canonical realmx_zmodType :=
  Eval hnf in ZmodType 'MR[R]_(m, n) realmx_zmodMixin.
Canonical realmx_of_zmodType :=
  Eval hnf in ZmodType (@realmx_t R m n) realmx_zmodMixin.
*)
End RealMxZmod.

(* -------------------------------------------------------------------- *)
Section RealMxRing.
Context {R : numDomainType} (m : nat).
(*
Definition realmx_ringMixin := [ringMixin of 'MR[R]_(m.+1, m.+1) by <:].
Canonical realmx_ringType :=
  Eval hnf in RingType 'MR[R]_(m.+1, m.+1) realmx_ringMixin.
Canonical realmx_of_ringType :=
  Eval hnf in RingType (@realmx_t R m.+1 m.+1) realmx_ringMixin.
*)
End RealMxRing.

(* -------------------------------------------------------------------- *)
Section RealMxRing.
Context {R : numDomainType} (m : nat).
(*
Definition realmx_unitRingMixin := [unitRingMixin of 'MR[R]_(m.+1, m.+1) by <:].
Canonical realmx_unitRingType :=
  Eval hnf in UnitRingType 'MR[R]_(m.+1, m.+1) realmx_unitRingMixin.
Canonical realmx_of_unitRingType :=
  Eval hnf in UnitRingType (@realmx_t R m.+1 m.+1) realmx_unitRingMixin.
*)
End RealMxRing.

(* -------------------------------------------------------------------- *)
Section HermMxType.
Context {R : numClosedFieldType} (m : nat).

Variant hermmx_t :=
  HermMx (M : 'M[R]_m) of (M \is hermmx).

Coercion hermmx_mx (M : hermmx_t) :=
  let: HermMx M _ := M in M.

Definition hermmx_isSub := Eval hnf in [isSub for hermmx_mx].
HB.instance Definition _ := hermmx_isSub.
HB.instance Definition _ := [Choice of hermmx_t by <:].

Lemma hermmx_inj : injective hermmx_mx. Proof. exact: val_inj. Qed.

(* Definition hermmx_of of phant R := hermmx_t.
Identity Coercion type_hermmx_of : hermmx_of >-> hermmx_t. *)
End HermMxType.

(* Bind Scope ring_scope with hermmx_of. *)
Bind Scope ring_scope with hermmx_t.

Arguments hermmx_mx {R m} M%R.
Arguments hermmx_inj {R m} [A%R B%R] : rename.

Notation "''MH[' R ]_ m " := (@hermmx_t R m)
  (at level 8, format "''MH[' R ]_ m").

(* -------------------------------------------------------------------- *)
Section HermMxOf.
Context {R : numClosedFieldType} (m : nat).

HB.instance Definition _ := [Choice of 'MH[R]_m by <:].

End HermMxOf.

Section HermMxZmod.
Context {R : numClosedFieldType} (m : nat).
(*
Definition hermmx_zmodMixin := [zmodMixin of 'MH[R]_m by <:].
Canonical hermmx_zmodType :=
  Eval hnf in ZmodType 'MH[R]_m hermmx_zmodMixin.
Canonical hermmx_of_zmodType :=
  Eval hnf in ZmodType (@hermmx_t R m) hermmx_zmodMixin.
*)
End HermMxZmod.


(* -------------------------------------------------------------------- *)
Section DenMxType.
Context {R : numClosedFieldType} (m : nat).

Variant denmx_t :=
  DenMx (M : 'M[R]_m) of (M \is denmx).

Coercion denmx_mx (M : denmx_t) :=
  let: DenMx M _ := M in M.

Definition denmx_isSub := Eval hnf in [isSub for denmx_mx].
HB.instance Definition _ := denmx_isSub.
HB.instance Definition _ := [Choice of denmx_t by <:].

Lemma denmx_inj : injective denmx_mx. Proof. exact: val_inj. Qed.

(* Definition denmx_of of phant R := denmx_t.
Identity Coercion type_denmx_of : denmx_of >-> denmx_t. *)
End DenMxType.

(* Bind Scope ring_scope with denmx_of. *)
Bind Scope ring_scope with denmx_t.

Arguments denmx_mx {R m} M%R.
Arguments denmx_inj {R m} [A%R B%R] : rename.

Notation "''MDen[' R ]_ m " := (@denmx_t R m)
  (at level 8, format "''MDen[' R ]_ m").

(* -------------------------------------------------------------------- *)
Section DenMxOf.
Context {R : numClosedFieldType} (m : nat).

HB.instance Definition _ := [Choice of 'MDen[R]_m by <:].

End DenMxOf.

(* -------------------------------------------------------------------- *)
Section ObsMxType.
Context {R : numClosedFieldType} (m : nat).

Variant obsmx_t :=
  ObsMx (M : 'M[R]_m) of (M \is obsmx).

Coercion obsmx_mx (M : obsmx_t) :=
  let: ObsMx M _ := M in M.

Definition obsmx_isSub := Eval hnf in [isSub for obsmx_mx].
HB.instance Definition _ := obsmx_isSub.
HB.instance Definition _ := [Choice of obsmx_t by <:].

Lemma obsmx_inj : injective obsmx_mx. Proof. exact: val_inj. Qed.

(* Definition obsmx_of of phant R := obsmx_t.
Identity Coercion type_obsmx_of : obsmx_of >-> obsmx_t. *)
End ObsMxType.

(* Bind Scope ring_scope with obsmx_of. *)
Bind Scope ring_scope with obsmx_t.

Arguments obsmx_mx {R m} M%R.
Arguments obsmx_inj {R m} [A%R B%R] : rename.

Notation "''MObs[' R ]_ m " := (@obsmx_t R m)
  (at level 8, format "''MObs[' R ]_ m").
(* Notation "''MObs[' R ]_ m " := (@obsmx_of _ m (Phant R))
  (at level 8, format "''MObs[' R ]_ m"). *)

(* -------------------------------------------------------------------- *)
Section ObsMxOf.
Context {R : numClosedFieldType} (m : nat).

HB.instance Definition _ := [Choice of 'MObs[R]_m by <:].

End ObsMxOf.

(* module for vector norm *)
HB.mixin Record isVNorm (R: numDomainType) (T : lmodType R) (mnorm : T -> R) := {
  lev_normD : forall x y, mnorm (x + y) <= mnorm x + mnorm y;
  normv0_eq0 : forall x, mnorm x = 0 -> x = 0;
  normvZ : forall a x, mnorm (a *: x) = `|a| * mnorm x;
}.

#[short(type="vnorm")]
HB.structure Definition VNorm (R: numDomainType) (T : lmodType R) :=
  { f of isVNorm R T f}.

Module VNormExports.
#[deprecated(since="mathcomp 2.0.0", note="Use VNorm.clone instead.")]
Notation "[ 'vnorm' 'of' T 'for' cT ]" := (VNorm.clone _ _ T%type cT)
  (at level 0, format "[ 'vnorm'  'of'  T  'for'  cT ]") : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use VNorm.clone instead.")]
Notation "[ 'vnorm' 'of' f ]" := (VNorm.clone _ _ f _)
  (at level 0, format "[ 'vnorm'  'of'  f ]") : form_scope.
End VNormExports.
HB.export VNormExports.

Section VNormTheory.
Context {R: numDomainType} {V: lmodType R} {mnorm : vnorm V}.
Local Notation "`[ x ]" := (mnorm x).

Lemma normv0 : `[ 0 ] = 0.
Proof. have <-: 0 *: 0 = (0 : V) by rewrite scaler0.
by rewrite normvZ normr0 mul0r. Qed.

Lemma normv0P A : reflect (`[ A ] = 0) (A == 0).
Proof. by apply: (iffP eqP)=> [->|/normv0_eq0 //]; apply: normv0. Qed.

Definition normv_eq0 A := sameP (`[ A ] =P 0) (normv0P A).

Lemma normvMn x n : `[ x *+ n] = `[x] *+ n.
Proof. by rewrite -scaler_nat normvZ normr_nat mulr_natl. Qed.
  
Lemma normvN x : `[ - x ] = `[ x ].
Proof. by rewrite -scaleN1r normvZ normrN normr1 mul1r. Qed.

Lemma normv_ge0 : forall x, `[ x ] >= 0.
Proof.
move=>x; move: (@lev_normD _ _ mnorm x (-x)).
by rewrite addrN normvN -mulr2n normv0 pmulrn_lge0.
Qed.

Lemma normv_nneg A : `[ A ] \is Num.nneg.
Proof. rewrite qualifE; exact: normv_ge0. Qed.

Lemma normv_real x : `[ x ] \is Num.real.
Proof. apply/ger0_real/normv_ge0. Qed.

Lemma normv_gt0 x : `[ x ] > 0 = (x != 0).
Proof. by rewrite lt_def normv_ge0 andbT normv_eq0. Qed.

Lemma lev_normB v w : `[v - w] <= `[v] + `[w].
Proof. by rewrite (le_trans (lev_normD _ _)) ?normvN. Qed.

Lemma lev_distD u v w : `[v-w] <= `[v-u] + `[u-w].
Proof. by rewrite (le_trans _ (lev_normD _ _)) // addrA addrNK. Qed.

Lemma levB_normD v w : `[v] - `[w] <= `[v+w].
Proof.
rewrite -{1}[v](addrK w) lterBDl.
by rewrite (le_trans (lev_normD _ _)) // addrC normvN.
Qed.

Lemma levB_dist v w : `[v] - `[w] <= `[v-w].
Proof. by rewrite -[`[w]]normvN levB_normD. Qed.

Lemma lev_dist_dist v w : `| `[v] - `[w] | <= `[v-w].
Proof.
have [ | | _ | _ ] // := @real_leP _ (mnorm v) (mnorm w); last by rewrite levB_dist.
1,2: by rewrite realE normv_ge0. by rewrite -(normvN (v-w)) opprB levB_dist.
Qed.

Lemma normv_sum (I: finType) (r : seq I) (P: pred I) f :
  mnorm (\sum_(i <- r | P i) f i) <= \sum_(i <- r | P i) mnorm (f i).
Proof.
elim: r => [|x r IH]; first by rewrite !big_nil normv0.
rewrite !big_cons. case: (P x)=>//.
apply (le_trans (lev_normD _ _)). by apply lerD.
Qed.

Definition cauchy_seqv  (u: nat -> V) := 
  forall e : R, 0 < e -> exists N : nat, 
    forall s t, (N <= s)%N -> (N <= t)%N -> mnorm (u s - u t) < e.

Lemma cauchy_seqv_cst x : cauchy_seqv (fun=>x).
by move=>e egt0; exists 0%N=> s t _ _; rewrite subrr normv0. Qed.

End VNormTheory.

Arguments cauchy_seqv {R V}.

Lemma normvZV {R: numFieldType} {V: lmodType R} {mnorm : vnorm V} (u : V) : 
  u != 0 -> mnorm ( (mnorm u)^-1 *: u ) = 1.
Proof.
by move=>Pu; rewrite normvZ ger0_norm ?invr_ge0 ?normv_ge0// mulVf// normv_eq0.
Qed.

#[short(type="porderLmodType")]
HB.structure Definition POrderedLmodule (R: ringType):=
  { T of Order.isPOrder ring_display T & GRing.Lmodule R T }.

(* module for vector order *)
HB.mixin Record POrderedLmodule_isVOrder (R: numDomainType)
 T of POrderedLmodule R T := {
  lev_add2rP : forall (z x y : T), x ⊑ y -> (x + z) ⊑ (y + z);
  lev_pscale2lP : forall (e : R) (x y : T), 0 < e -> x ⊑ y -> (e *: x) ⊑ (e *: y);
}.

#[short(type="vorderType")]
HB.structure Definition VOrder (R: numDomainType) :=
  { T of POrderedLmodule R T & POrderedLmodule_isVOrder R T }.

Module VOrderExports.
#[deprecated(since="mathcomp 2.0.0", note="Use VOrder.clone instead.")]
Notation "[ 'vorderType' R 'of' T 'for' cT ]" := (VOrder.clone R T%type cT)
  (at level 0, format "[ 'vorderType'  R  'of'  T  'for'  cT ]") : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use VOrder.clone instead.")]
Notation "[ 'vorderType' R 'of' T ]" :=  (VOrder.clone R T%type _)
  (at level 0, format "[ 'vorderType'  R  'of'  T ]") : form_scope.
End VOrderExports.
HB.export VOrderExports.

HB.mixin Record VOrder_isCan (R: numFieldType) T of VOrder R T := {
  pscalev_lge0 : forall (x : T) (e : R), 0 ⊏ x -> 0 ⊑ (e *: x) = (0 <= e);
}.

#[short(type="canVOrderType")]
HB.structure Definition CanVOrder (R: numFieldType) :=
  { T of VOrder R T & VOrder_isCan R T}.

Module CanVOrderExports.
#[deprecated(since="mathcomp 2.0.0", note="Use CanVOrder.clone instead.")]
Notation "[ 'canVOrderType' R 'of' T 'for' cT ]" := (VOrder.clone R T%type cT)
  (at level 0, format "[ 'canVOrderType'  R  'of'  T  'for'  cT ]") : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use CanVOrder.clone instead.")]
Notation "[ 'canVOrderType' R 'of' T ]" :=  (VOrder.clone R T%type _)
  (at level 0, format "[ 'canVOrderType'  R  'of'  T ]") : form_scope.
End CanVOrderExports.
HB.export CanVOrderExports.

Lemma scalerNN (R : ringType) (V : lmodType R) (a : R) (x : V) : 
  (- a) *: (- x) = a *: x.
Proof. by rewrite scalerN scaleNr opprK. Qed.

Section VOrderTheory.
Variable (R: numDomainType) (T : vorderType R).
Implicit Type (x y z : T) (a b c : R).
Local Notation "'0" := (0 : T).

Lemma subv_ge0 x y : ('0 ⊑ x - y) = (y ⊑ x).
Proof. 
apply/Bool.eq_iff_eq_true; split=>[/(@lev_add2rP R T y)|/(@lev_add2rP R T(-y))];
by rewrite ?addrNK ?add0r// addrN.
Qed.

Lemma subv_gt0 x y : ('0 ⊏ y - x) = (x ⊏ y).
Proof. by rewrite !lt_def subr_eq0 subv_ge0. Qed.
Lemma subv_le0  x y : (y - x ⊑ 0) = (y ⊑ x).
Proof. by rewrite -[LHS]subv_ge0 opprB add0r subv_ge0. Qed.
Lemma subv_lt0  x y : (y - x ⊏ 0) = (y ⊏ x).
Proof. by rewrite -[LHS]subv_gt0 opprB add0r subv_gt0. Qed.

Definition subv_lte0 := (subv_le0, subv_lt0).
Definition subv_gte0 := (subv_ge0, subv_gt0).
Definition subv_cp0 := (subv_lte0, subv_gte0).

Lemma levN2 : {mono (-%R : T -> T) : x y /~ x ⊑ y }.
Proof. by move=>x y; rewrite -subv_ge0 opprK addrC subv_ge0. Qed.
Hint Resolve levN2 : core.

Lemma ltvN2 : {mono (-%R : T -> T) : x y /~ x ⊏ y }.
Proof. by move=> x y /=; rewrite leW_nmono. Qed.
Hint Resolve ltvN2 : core.
Definition ltev_opp2 := (levN2, ltvN2).

Lemma addv_ge0 x y : '0 ⊑ x -> '0 ⊑ y -> '0 ⊑ x + y.
Proof.
by move=>P1 P2; apply: (le_trans P1); rewrite -subv_ge0 addrC addrA addNr add0r.
Qed.

Lemma addv_gt0 x y : '0 ⊏ x -> '0 ⊏ y -> '0 ⊏ x + y.
Proof.
rewrite !lt_def=>/andP[/negPf Pf Pf1]/andP[Pg Pg1]; rewrite (addv_ge0 Pf1 Pg1) andbT.
case: eqP=>//= P1; move: Pg1; rewrite -P1 -subv_ge0 opprD addrC addrNK -oppr0 levN2=>P2.
by rewrite -Pf eq_le Pf1 P2.
Qed.

Lemma le0v x : ('0 ⊑ x) = (x == 0) || ('0 ⊏ x).
Proof. by rewrite lt_def; case: eqP => // ->; rewrite lexx. Qed.

Lemma levD2r x : {mono +%R^~ x : y z / y ⊑ z}.
Proof. by move=>y z; rewrite -subv_ge0 opprD addrACA addrN addr0 subv_ge0. Qed.

Lemma levNr x y : (x ⊑ - y) = (y ⊑ - x).
Proof. by rewrite (monoRL opprK levN2). Qed.

Lemma ltv_oppr x y : (x ⊏ - y) = (y ⊏ - x).
Proof. by rewrite (monoRL opprK (leW_nmono levN2)). Qed.

Definition ltev_oppr := (levNr, ltv_oppr).

Lemma levNl x y : (- x ⊑ y) = (- y ⊑ x).
Proof. by rewrite (monoLR opprK levN2). Qed.

Lemma ltvNl x y : (- x ⊏ y) = (- y ⊏ x).
Proof. by rewrite (monoLR opprK (leW_nmono levN2)). Qed.

Definition ltev_oppl := (levNl, ltvNl).

Lemma oppv_ge0 x : ('0 ⊑ - x) = (x ⊑ 0).
Proof. by rewrite ltev_oppr oppr0. Qed.

Lemma oppv_gt0 x : ('0 ⊏ - x) = (x ⊏ 0).
Proof. by rewrite ltev_oppr oppr0. Qed.

Definition oppv_gte0 := (oppv_ge0, oppv_gt0).

Lemma oppv_le0 x : (- x ⊑ 0) = ('0 ⊑ x).
Proof. by rewrite ltev_oppl oppr0. Qed.

Lemma oppv_lt0 x : (- x ⊏ 0) = ('0 ⊏ x).
Proof. by rewrite ltev_oppl oppr0. Qed.

Definition oppv_lte0 := (oppv_le0, oppv_lt0).
Definition oppv_cp0 := (oppv_gte0, oppv_lte0).
Definition ltevNE := (oppv_cp0, ltev_opp2).

Lemma gev0_cp x : '0 ⊑ x -> (- x ⊑ 0) * (- x ⊑ x).
Proof. by move=> hx; rewrite oppv_cp0 hx (@le_trans _ _ '0) ?oppv_cp0. Qed.

Lemma gtv0_cp x : '0 ⊏ x ->
  ('0 ⊑ x) * (- x ⊑ 0) * (- x ⊑ x) * (- x ⊏ 0) * (- x ⊏ x).
Proof.
move=> hx; move: (ltW hx) => hx'; rewrite !gev0_cp hx'=>[//|//|].
by rewrite oppv_cp0 hx (@lt_trans _ _ '0) ?oppv_cp0.
Qed.

Lemma lev0_cp x : x ⊑ 0 -> ('0 ⊑ - x) * (x ⊑ - x).
Proof. by move=> hx; rewrite oppv_cp0 hx (@le_trans _ _ '0) ?oppv_cp0. Qed.

Lemma ltv0_cp x :
  x ⊏ 0 -> (x ⊑ 0) * ('0 ⊑ - x) * (x ⊑ - x) * ('0 ⊏ - x) * (x ⊏ - x).
Proof.
move=> hx; move: (ltW hx) => hx'; rewrite !lev0_cp hx' =>[//|//|].
by rewrite oppv_cp0 hx (@lt_trans _ _ '0) ?oppv_cp0.
Qed.

(* Monotony of addition *)
Lemma levD2l x : {mono +%R x : y z / y ⊑ z}.
Proof. by move=>y z; rewrite ![x + _]addrC levD2r. Qed.

Lemma ltv_add2l x : {mono +%R x : y z / y ⊏ z}.
Proof. by move=> y z /=; rewrite (leW_mono (levD2l _)). Qed.

Lemma ltv_add2r x : {mono +%R^~ x : y z / y ⊏ z}.
Proof. by move=> y z /=; rewrite (leW_mono (levD2r _)). Qed.

Definition levD2 := (levD2l, levD2r).
Definition ltvD2 := (ltv_add2l, ltv_add2r).
Definition ltev_add2 := (levD2, ltvD2).

(* Addition, subtraction and transitivity *)
Lemma levD x y z t : x ⊑ y -> z ⊑ t -> x + z ⊑ y + t.
Proof. by move=> lxy lzt; rewrite (@le_trans _ _ (y + z)) ?ltev_add2. Qed.

Lemma lev_lt_add x y z t : x ⊑ y -> z ⊏ t -> x + z ⊏ y + t.
Proof. by move=> lxy lzt; rewrite (@le_lt_trans _ _ (y + z)) ?ltev_add2. Qed.

Lemma ltv_le_add x y z t : x ⊏ y -> z ⊑ t -> x + z ⊏ y + t.
Proof. by move=> lxy lzt; rewrite (@lt_le_trans _ _ (y + z)) ?ltev_add2. Qed.

Lemma ltvD x y z t : x ⊏ y -> z ⊏ t -> x + z ⊏ y + t.
Proof. by move=> lxy lzt; rewrite ltv_le_add ?ltW. Qed.

Lemma levB x y z t : x ⊑ y -> t ⊑ z -> x - z ⊑ y - t.
Proof. by move=> lxy ltz; rewrite levD ?ltev_opp2. Qed.

Lemma lev_lt_sub x y z t : x ⊑ y -> t ⊏ z -> x - z ⊏ y - t.
Proof. by move=> lxy lzt; rewrite lev_lt_add ?ltev_opp2. Qed.

Lemma ltv_le_sub x y z t : x ⊏ y -> t ⊑ z -> x - z ⊏ y - t.
Proof. by move=> lxy lzt; rewrite ltv_le_add ?ltev_opp2. Qed.

Lemma ltv_sub x y z t : x ⊏ y -> t ⊏ z -> x - z ⊏ y - t.
Proof. by move=> lxy lzt; rewrite ltvD ?ltev_opp2. Qed.

Lemma levBlDr x y z : (x - y ⊑ z) = (x ⊑ z + y).
Proof. by rewrite (monoLR (addrK _) (levD2r _)). Qed.

Lemma ltvBlDr x y z : (x - y ⊏ z) = (x ⊏ z + y).
Proof. by rewrite (monoLR (addrK _) (ltv_add2r _)). Qed.

Lemma levBrDr x y z : (x ⊑ y - z) = (x + z ⊑ y).
Proof. by rewrite (monoLR (addrNK _) (levD2r _)). Qed.

Lemma ltvBrDr x y z : (x ⊏ y - z) = (x + z ⊏ y).
Proof. by rewrite (monoLR (addrNK _) (ltv_add2r _)). Qed.

Definition lev_sub_addr := (levBlDr, levBrDr).
Definition ltv_sub_addr := (ltvBlDr, ltvBrDr).
Definition ltev_sub_addr := (lev_sub_addr, ltv_sub_addr).

Lemma levBlDl x y z : (x - y ⊑ z) = (x ⊑ y + z).
Proof. by rewrite ltev_sub_addr addrC. Qed.

Lemma ltvBlDl x y z : (x - y ⊏ z) = (x ⊏ y + z).
Proof. by rewrite ltev_sub_addr addrC. Qed.

Lemma levBrDl x y z : (x ⊑ y - z) = (z + x ⊑ y).
Proof. by rewrite ltev_sub_addr addrC. Qed.

Lemma ltvBrDl x y z : (x ⊏ y - z) = (z + x ⊏ y).
Proof. by rewrite ltev_sub_addr addrC. Qed.

Definition lev_sub_addl := (levBlDl, levBrDl).
Definition ltv_sub_addl := (ltvBlDl, ltvBrDl).
Definition ltevBDl := (lev_sub_addl, ltv_sub_addl).

Lemma levDl x y : (x ⊑ x + y) = ('0 ⊑ y).
Proof. by rewrite -{1}[x]addr0 ltev_add2. Qed.

Lemma ltvDl x y : (x ⊏ x + y) = ('0 ⊏ y).
Proof. by rewrite -{1}[x]addr0 ltev_add2. Qed.

Lemma levDr x y : (x ⊑ y + x) = ('0 ⊑ y).
Proof. by rewrite -{1}[x]add0r ltev_add2. Qed.

Lemma ltv_addr x y : (x ⊏ y + x) = ('0 ⊏ y).
Proof. by rewrite -{1}[x]add0r ltev_add2. Qed.

Lemma gev_addl x y : (x + y ⊑ x) = (y ⊑ 0).
Proof. by rewrite -{2}[x]addr0 ltev_add2. Qed.

Lemma gtv_addl x y : (x + y ⊏ x) = (y ⊏ 0).
Proof. by rewrite -{2}[x]addr0 ltev_add2. Qed.

Lemma gev_addr x y : (y + x ⊑ x) = (y ⊑ 0).
Proof. by rewrite -{2}[x]add0r ltev_add2. Qed.

Lemma gtv_addr x y : (y + x ⊏ x) = (y ⊏ 0).
Proof. by rewrite -{2}[x]add0r ltev_add2. Qed.

Definition cpv_add := (levDl, levDr, gev_addl, gev_addl,
                       ltvDl, ltv_addr, gtv_addl, gtv_addl).

(* Addition with levt member knwon to be positive/negative *)
Lemma lev_paddl y x z : '0 ⊑ x -> y ⊑ z -> y ⊑ x + z.
Proof. by move=> *; rewrite -[y]add0r levD. Qed.

Lemma ltv_wpDl y x z : '0 ⊑ x -> y ⊏ z -> y ⊏ x + z.
Proof. by move=> *; rewrite -[y]add0r lev_lt_add. Qed.

Lemma ltv_spaddl y x z : '0 ⊏ x -> y ⊑ z -> y ⊏ x + z.
Proof. by move=> *; rewrite -[y]add0r ltv_le_add. Qed.

Lemma ltv_spsaddl y x z : '0 ⊏ x -> y ⊏ z -> y ⊏ x + z.
Proof. by move=> *; rewrite -[y]add0r ltvD. Qed.

Lemma lev_wnDl y x z : x ⊑ 0 -> y ⊑ z -> x + y ⊑ z.
Proof. by move=> *; rewrite -[z]add0r levD. Qed.

Lemma ltv_naddl y x z : x ⊑ 0 -> y ⊏ z -> x + y ⊏ z.
Proof. by move=> *; rewrite -[z]add0r lev_lt_add. Qed.

Lemma ltv_snaddl y x z : x ⊏ 0 -> y ⊑ z -> x + y ⊏ z.
Proof. by move=> *; rewrite -[z]add0r ltv_le_add. Qed.

Lemma ltv_snsaddl y x z : x ⊏ 0 -> y ⊏ z -> x + y ⊏ z.
Proof. by move=> *; rewrite -[z]add0r ltvD. Qed.

(* Addition with right member we know positive/negative *)
Lemma lev_wpDr y x z : '0 ⊑ x -> y ⊑ z -> y ⊑ z + x.
Proof. by move=> *; rewrite [_ + x]addrC lev_paddl. Qed.

Lemma ltv_wpDr y x z : '0 ⊑ x -> y ⊏ z -> y ⊏ z + x.
Proof. by move=> *; rewrite [_ + x]addrC ltv_wpDl. Qed.

Lemma ltv_spaddr y x z : '0 ⊏ x -> y ⊑ z -> y ⊏ z + x.
Proof. by move=> *; rewrite [_ + x]addrC ltv_spaddl. Qed.

Lemma ltv_spsaddr y x z : '0 ⊏ x -> y ⊏ z -> y ⊏ z + x.
Proof. by move=> *; rewrite [_ + x]addrC ltv_spsaddl. Qed.

Lemma lev_naddr y x z : x ⊑ 0 -> y ⊑ z -> y + x ⊑ z.
Proof. by move=> *; rewrite [_ + x]addrC lev_wnDl. Qed.

Lemma ltv_naddr y x z : x ⊑ 0 -> y ⊏ z -> y + x ⊏ z.
Proof. by move=> *; rewrite [_ + x]addrC ltv_naddl. Qed.

Lemma ltv_snaddr y x z : x ⊏ 0 -> y ⊑ z -> y + x ⊏ z.
Proof. by move=> *; rewrite [_ + x]addrC ltv_snaddl. Qed.

Lemma ltv_snsaddr y x z : x ⊏ 0 -> y ⊏ z -> y + x ⊏ z.
Proof. by move=> *; rewrite [_ + x]addrC ltv_snsaddl. Qed.

(* x and y have the same sign and their sum is null *)
Lemma paddv_eq0 x y :
  '0 ⊑ x -> '0 ⊑ y -> (x + y == 0) = (x == 0) && (y == 0).
Proof.
rewrite le0v; case/orP=> [/eqP->|hx]; first by rewrite add0r eqxx.
by rewrite (gt_eqF hx) /= => hy; rewrite gt_eqF ?ltv_spaddl.
Qed.

Lemma naddv_eq0 x y :
  x ⊑ 0 -> y ⊑ 0 -> (x + y == 0) = (x == 0) && (y == 0).
Proof.
by move=> lex0 ley0; rewrite -oppr_eq0 opprD paddv_eq0 ?oppv_cp0 ?oppr_eq0.
Qed.

Lemma addv_ss_eq0 x y :
    ('0 ⊑ x) && ('0 ⊑ y) || (x ⊑ 0) && (y ⊑ 0) ->
  (x + y == 0) = (x == 0) && (y == 0).
Proof. by case/orP=> /andP []; [apply: paddv_eq0 | apply: naddv_eq0]. Qed.

(* big sum and lev *)
Lemma sumv_ge0 I (r : seq I) (P : pred I) (F : I -> T) :
  (forall i, P i -> ('0 ⊑ F i)) -> '0 ⊑ \sum_(i <- r | P i) (F i).
Proof. exact: (@big_ind T _ '0 _ (lexx '0) (@lev_paddl '0)). Qed.  

Lemma lev_sum I (r : seq I) (P : pred I) (F G : I -> T) :
    (forall i, P i -> F i ⊑ G i) ->
  \sum_(i <- r | P i) F i ⊑ \sum_(i <- r | P i) G i.
Proof. exact: (big_ind2 _ (lexx _) levD). Qed.

Lemma lev_sum_nat (m n : nat) (F G : nat -> T) :
  (forall i, (m <= i < n)%N -> F i ⊑ G i) ->
  \sum_(m <= i < n) F i ⊑ \sum_(m <= i < n) G i.
Proof. by move=> le_FG; rewrite !big_nat lev_sum. Qed.

Lemma psumv_eq0 (I : eqType) (r : seq I) (P : pred I) (F : I -> T) :
    (forall i, P i -> '0 ⊑ F i) ->
  (\sum_(i <- r | P i) (F i) == 0) = (all (fun i => (P i) ==> (F i == 0)) r).
Proof.
elim: r=> [|a r ihr hr] /=; rewrite (big_nil, big_cons); first by rewrite eqxx.
by case: ifP=> pa /=; rewrite ?paddv_eq0 ?ihr ?hr ?sumv_ge0.
Qed.

(* :TODO: Cyril : See which form to keep *)
Lemma psumv_eq0P (I : finType) (P : pred I) (F : I -> T) :
     (forall i, P i -> '0 ⊑ F i) -> \sum_(i | P i) F i = 0 ->
  (forall i, P i -> F i = 0).
Proof.
move=> F_ge0 /eqP; rewrite psumv_eq0=>[//|].
rewrite -big_all big_andE => /forallP hF i Pi.
by move: (hF i); rewrite implyTb Pi /= => /eqP.
Qed.

Lemma lt0v x : ('0 ⊏ x) = (x != 0) && ('0 ⊑ x). Proof. by rewrite lt_def. Qed.

Lemma lt0v_neq0 x : '0 ⊏ x -> x != 0.
Proof. by rewrite lt0v; case/andP. Qed.

Lemma ltv0_neq0 x : x ⊏ 0 -> x != 0.
Proof. by rewrite lt_neqAle; case/andP. Qed.

End VOrderTheory.

Section VOrderFieldTheory.
Variable (R: numFieldType) (T : vorderType R).
Implicit Type (x y z : T) (a b c : R).
Local Notation "'0" := (0 : T).

Lemma pscalev_rge0 a y : 0 < a -> ('0 ⊑ a *: y) = ('0 ⊑ y).
Proof.
move=>Pa; apply/Bool.eq_iff_eq_true; split=>P.
have P1 : (a^-1 * a) = 1 by rewrite mulVf// lt0r_neq0.
by rewrite -[y]scale1r -(scaler0 _ a^-1) -P1 -scalerA lev_pscale2lP// invr_gt0.
by rewrite -(scaler0 _ a) lev_pscale2lP.
Qed.

Lemma pscalev_rgt0 a y : 0 < a -> ('0 ⊏ a *: y) = ('0 ⊏ y).
Proof.
by move=>Pa; move: {+}Pa; rewrite !lt_def 
  scaler_eq0 negb_or pscalev_rge0// =>/andP[->_/=].
Qed.

(* mulr and lev/ltv *)
Lemma lev_pscale2l a : 0 < a -> {mono ( *:%R a : T -> T) : x y / x ⊑ y}.
Proof.
by move=> x_gt0 y z /=; rewrite -subv_ge0 -scalerBr pscalev_rge0// subv_ge0.
Qed.

Lemma ltv_pscale2l a : 0 < a -> {mono ( *:%R a : T -> T) : x y / x ⊏ y}.
Proof. by move=> x_gt0; apply: leW_mono (lev_pscale2l _). Qed.

Definition ltev_pscale2l := (lev_pscale2l, ltv_pscale2l).

Lemma lev_nscale2l a : a < 0 -> {mono ( *:%R a : T -> T) : x y /~ x ⊑ y}.
Proof.
by move=> x_lt0 y z /=; rewrite -levN2 -!scaleNr lev_pscale2l ?oppr_gt0.
Qed.

Lemma ltv_nscale2l a : a < 0 -> {mono ( *:%R a : T -> T) : x y /~ x ⊏ y}.
Proof. by move=> x_lt0; apply: leW_nmono (lev_nscale2l _). Qed.

Definition ltev_nscale2l := (lev_nscale2l, ltv_nscale2l).

Lemma lev_wpscale2l a : 0 <= a -> {homo ( *:%R a : T -> T) : y z / y ⊑ z}.
Proof.
by rewrite le0r => /orP[/eqP-> y z | /lev_pscale2l/mono2W//]; rewrite !scale0r.
Qed.

Lemma lev_wpscale2r x : '0 ⊑ x -> {homo *:%R^~ x : y z / (y <= z)%O}.
Proof.
move=>x_ge0 a b; rewrite -subr_ge0 -subv_ge0 -scalerBl le0r.
by move=>/orP[/eqP->|/(pscalev_rge0 x)->//]; rewrite scale0r.
Qed.

Lemma lev_wnscale2l a : a <= 0 -> {homo ( *:%R a : T -> T) : y z /~ y ⊑ z}.
Proof.
by move=> x_le0 y z leyz; rewrite -![a *: _]scalerNN lev_wpscale2l ?ltevNE// lterNE.
Qed.

Lemma lev_wnscale2r x : x ⊑ 0 -> {homo *:%R^~ x : y z /~ (y <= z)%O}.
Proof.
by move=> x_le0 y z leyz; rewrite -![_ *: x]scalerNN lev_wpscale2r ?ltevNE// lterNE.
Qed.

(* Binary forms, for backchaining. *)

Lemma lev_pscale2 a b x y :
  0 <= a -> '0 ⊑ x -> a <= b -> x ⊑ y -> a *: x ⊑ b *: y.
Proof.
move=> x1ge0 x2ge0 le_xy1 le_xy2; have y1ge0 := le_trans x1ge0 le_xy1.
exact: le_trans (lev_wpscale2r x2ge0 le_xy1) (lev_wpscale2l y1ge0 le_xy2).
Qed.

Lemma ltv_pscale2 a b x y :
  0 <= a -> '0 ⊑ x -> a < b -> x ⊏ y -> a *: x ⊏ b *: y.
Proof.
move=> x1ge0 x2ge0 lt_xy1 lt_xy2; have y1gt0 := le_lt_trans x1ge0 lt_xy1.
by rewrite (le_lt_trans (lev_wpscale2r x2ge0 (ltW lt_xy1))) ?ltv_pscale2l.
Qed.

(* complement for x *+ n and <= or < *)
Local Notation natmul := (@GRing.natmul T).

Lemma lev_pmuln2r n : (0 < n)%N -> {mono natmul^~ n : x y / x ⊑ y}.
Proof.
by case: n => // n _ x y /=; rewrite -!scaler_nat lev_pscale2l ?ltr0n.
Qed.

Lemma ltv_pmuln2r n : (0 < n)%N -> {mono natmul^~ n : x y / x ⊏ y}.
Proof. by move/lev_pmuln2r/leW_mono. Qed.

Lemma pmulvnI n : (0 < n)%N -> injective (natmul^~ n).
Proof. by move/lev_pmuln2r/inc_inj. Qed.

Lemma eqr_pmuln2r n : (0 < n)%N -> {mono natmul^~ n : x y / x == y}.
Proof. by move/pmulvnI/inj_eq. Qed.

Lemma pmulvn_lgt0 x n : (0 < n)%N -> ('0 ⊏ x *+ n) = ('0 ⊏ x).
Proof. by move=> n_gt0; rewrite -(mul0rn _ n) ltv_pmuln2r // mul0rn. Qed.

Lemma pmulvn_llt0 x n : (0 < n)%N -> (x *+ n ⊏ 0) = (x ⊏ 0).
Proof. by move=> n_gt0; rewrite -(mul0rn _ n) ltv_pmuln2r // mul0rn. Qed.

Lemma pmulvn_lge0 x n : (0 < n)%N -> ('0 ⊑ x *+ n) = ('0 ⊑ x).
Proof. by move=> n_gt0; rewrite -(mul0rn _ n) lev_pmuln2r // mul0rn. Qed.

Lemma pmulvn_lle0 x n : (0 < n)%N -> (x *+ n ⊑ 0) = (x ⊑ 0).
Proof. by move=> n_gt0; rewrite -(mul0rn _ n) lev_pmuln2r // mul0rn. Qed.

Lemma ltv_wmuln2r x y n : x ⊏ y -> (x *+ n ⊏ y *+ n) = (0 < n)%N.
Proof. by move=> ltxy; case: n=> // n; rewrite ltv_pmuln2r. Qed.

Lemma ltv_wpmuln2r n : (0 < n)%N -> {homo natmul^~ n : x y / x ⊏ y}.
Proof. by move=> n_gt0 x y /= / ltv_wmuln2r ->. Qed.

Lemma lev_wMn2r n : {homo natmul^~ n : x y / x ⊑ y}.
Proof. by move=> x y hxy /=; case: n=> // n; rewrite lev_pmuln2r. Qed.

Lemma mulvn_wge0 x n : '0 ⊑ x -> '0 ⊑ x *+ n.
Proof. by move=> /(lev_wMn2r n); rewrite mul0rn. Qed.

Lemma mulvn_wle0 x n : x ⊑ 0 -> x *+ n ⊑ 0.
Proof. by move=> /(lev_wMn2r n); rewrite mul0rn. Qed.

Lemma lev_muln2r n x y : (x *+ n ⊑ y *+ n) = ((n == 0%N) || (x ⊑ y)).
Proof. by case: n => [|n]; rewrite ?lexx ?eqxx // lev_pmuln2r. Qed.

Lemma ltv_muln2r n x y : (x *+ n ⊏ y *+ n) = ((0 < n)%N && (x ⊏ y)).
Proof. by case: n => [|n]; rewrite ?lexx ?eqxx // ltv_pmuln2r. Qed.

Lemma eqv_muln2r n x y : (x *+ n == y *+ n) = (n == 0)%N || (x == y).
Proof. by rewrite {1}eq_le [x == _]eq_le !lev_muln2r -orb_andr. Qed.

(* More characteristic zero properties. *)

Lemma mulvn_eq0 x n : (x *+ n == 0) = ((n == 0)%N || (x == 0)).
Proof. by rewrite -{1}(mul0rn T n) eqv_muln2r. Qed.

Lemma eqNv x : (- x == x) = (x == 0).
Proof. by rewrite eq_sym -addr_eq0 -mulr2n mulvn_eq0. Qed.

Lemma mulvIn x : x != 0 -> injective (GRing.natmul x).
Proof.
move=> x_neq0 m n; without loss /subnK <-: m n / (n <= m)%N.
  by move=> IH eq_xmn; case/orP: (leq_total m n) => /IH->.
by move/eqP; rewrite mulrnDr -subr_eq0 addrK mulvn_eq0 => /predU1P[-> | /idPn].
Qed.

Lemma lev_wpmuln2l x :
  '0 ⊑ x -> {homo (natmul x) : m n / (m <= n)%N >-> m ⊑ n}.
Proof. by move=> xge0 m n /subnK <-; rewrite mulrnDr lev_paddl ?mulvn_wge0. Qed.

Lemma lev_wnmuln2l x :
  x ⊑ 0 -> {homo (natmul x) : m n / (n <= m)%N >-> m ⊑ n}.
Proof.
by move=> xle0 m n hmn /=; rewrite -levN2 -!mulNrn lev_wpmuln2l // oppv_cp0.
Qed.

Lemma mulvn_wgt0 x n : '0 ⊏ x -> '0 ⊏ x *+ n = (0 < n)%N.
Proof. by case: n => // n hx; rewrite pmulvn_lgt0. Qed.

Lemma mulvn_wlt0 x n : x ⊏ 0 -> x *+ n ⊏ 0 = (0 < n)%N.
Proof. by case: n => // n hx; rewrite pmulvn_llt0. Qed.

Lemma lev_pmuln2l x :
  '0 ⊏ x -> {mono (natmul x) : m n / (m <= n)%N >-> m ⊑ n}.
Proof.
move=> x_gt0 m n /=; case: leqP => hmn; first by rewrite lev_wpmuln2l // ltW.
rewrite -(subnK (ltnW hmn)) mulrnDr gev_addr lt_geF //.
by rewrite mulvn_wgt0 // subn_gt0.
Qed.

Lemma ltv_pmuln2l x :
  '0 ⊏ x -> {mono (natmul x) : m n / (m < n)%N >-> m ⊏ n}.
Proof. by move=> x_gt0; apply: leW_mono (lev_pmuln2l _). Qed.

Lemma lev_nmuln2l x :
  x ⊏ 0 -> {mono (natmul x) : m n / (n <= m)%N >-> m ⊑ n}.
Proof.
by move=> x_lt0 m n /=; rewrite -levN2 -!mulNrn lev_pmuln2l // oppv_gt0.
Qed.

Lemma ltv_nmuln2l x :
  x ⊏ 0 -> {mono (natmul x) : m n / (n < m)%N >-> m ⊏ n}.
Proof. by move=> x_lt0; apply: leW_nmono (lev_nmuln2l _). Qed.

Lemma pmulvn_rgt0 x n : '0 ⊏ x -> '0 ⊏ x *+ n = (0 < n)%N.
Proof. by move=> x_gt0; rewrite -(mulr0n x) ltv_pmuln2l. Qed.

Lemma pmulvn_rlt0 x n : '0 ⊏ x -> x *+ n ⊏ 0 = false.
Proof. by move=> x_gt0; rewrite -(mulr0n x) ltv_pmuln2l. Qed.

Lemma pmulvn_rge0 x n : '0 ⊏ x -> '0 ⊑ x *+ n.
Proof. by move=> x_gt0; rewrite -(mulr0n x) lev_pmuln2l. Qed.

Lemma pmulvn_rle0 x n : '0 ⊏ x -> x *+ n ⊑ 0 = (n == 0)%N.
Proof. by move=> x_gt0; rewrite -(mulr0n x) lev_pmuln2l ?leqn0. Qed.

Lemma nmulvn_rgt0 x n : x ⊏ 0 -> '0 ⊏ x *+ n = false.
Proof. by move=> x_lt0; rewrite -(mulr0n x) ltv_nmuln2l. Qed.

Lemma nmulvn_rge0 x n : x ⊏ 0 -> '0 ⊑ x *+ n = (n == 0)%N.
Proof. by move=> x_lt0; rewrite -(mulr0n x) lev_nmuln2l ?leqn0. Qed.

Lemma nmulvn_rle0 x n : x ⊏ 0 -> x *+ n ⊑ 0.
Proof. by move=> x_lt0; rewrite -(mulr0n x) lev_nmuln2l. Qed.

(* Remark : pscalev_rgt0 and pscalev_rge0 are defined above *)

(* a positive and y right *)
Lemma pscalev_rlt0 a y : 0 < a -> (a *: y ⊏ 0) = (y ⊏ 0).
Proof. by move=> x_gt0; rewrite -!oppv_gt0 -scalerN pscalev_rgt0 // oppr_gt0. Qed.

Lemma pscalev_rle0 a y : 0 < a -> (a *: y ⊑ 0) = (y ⊑ 0).
Proof. by move=> x_gt0; rewrite -!oppv_ge0 -scalerN pscalev_rge0 // oppr_ge0. Qed.

(* a negative and y right *)
Lemma nscalev_rgt0 a y : a < 0 -> ('0 ⊏ a *: y) = (y ⊏ 0).
Proof. by move=> x_lt0; rewrite -scalerNN pscalev_rgt0 ?ltevNE// lterNE. Qed.

Lemma nscalev_rge0 a y : a < 0 -> ('0 ⊑ a *: y) = (y ⊑ 0).
Proof. by move=> x_lt0; rewrite -scalerNN pscalev_rge0 ?ltevNE// lterNE. Qed.

Lemma nscalev_rlt0 a y : a < 0 -> (a *: y ⊏ 0) = ('0 ⊏ y).
Proof. by move=> x_lt0; rewrite -scalerNN pscalev_rlt0 ?ltevNE// lterNE. Qed.

Lemma nscalev_rle0 a y : a < 0 -> (a *: y ⊑ 0) = ('0 ⊑ y).
Proof. by move=> x_lt0; rewrite -scalerNN pscalev_rle0 ?ltevNE// lterNE. Qed.

(* weak and symmetric lemmas *)
Lemma scalev_ge0 a y : 0 <= a -> '0 ⊑ y -> '0 ⊑ a *: y.
Proof. by move=> x_ge0 y_ge0; rewrite -(scaler0 _ a) lev_wpscale2l. Qed.

Lemma scalev_le0 a y : a <= 0 -> y ⊑ 0 -> '0 ⊑ a *: y.
Proof. by move=> x_le0 y_le0; rewrite -(scaler0 _ a) lev_wnscale2l. Qed.

Lemma scalev_ge0_le0 a y : 0 <= a -> y ⊑ 0 -> a *: y ⊑ 0.
Proof. by move=> x_le0 y_le0; rewrite -(scaler0 _ a) lev_wpscale2l. Qed.

Lemma scalev_le0_ge0 a y : a <= 0 -> '0 ⊑ y -> a *: y ⊑ 0.
Proof. by move=> x_le0 y_le0; rewrite -(scaler0 _ a) lev_wnscale2l. Qed.

(* scalev_gt0 with only one case *)

Lemma scalev_gt0 a x : 0 < a -> '0 ⊏ x -> '0 ⊏ a *: x.
Proof. by move=> x_gt0 y_gt0; rewrite pscalev_rgt0. Qed.

Lemma scalev_lt0 a x : a < 0 -> x ⊏ 0 -> '0 ⊏ a *: x.
Proof. by move=> x_le0 y_le0; rewrite nscalev_rgt0. Qed.

Lemma scalev_gt0_lt0 a x : 0 < a -> x ⊏ 0 -> a *: x ⊏ 0.
Proof. by move=> x_le0 y_le0; rewrite pscalev_rlt0. Qed.

Lemma scalev_lt0_gt0 a x : a < 0 -> '0 ⊏ x -> a *: x ⊏ 0.
Proof. by move=> x_le0 y_le0; rewrite nscalev_rlt0. Qed.

(* lev/ltv and multiplication between a positive/negative
   and a exterior (1 <= _) or interior (0 <= _ <= 1) *)

Lemma lev_pescale a x : '0 ⊑ x -> 1 <= a -> x ⊑ a *: x.
Proof. by move=> hy hx; rewrite -{1}[x]scale1r lev_wpscale2r. Qed.

Lemma lev_nescale a x : x ⊑ 0 -> 1 <= a -> a *: x ⊑ x.
Proof. by move=> hy hx; rewrite -{2}[x]scale1r lev_wnscale2r. Qed.

Lemma lev_piscale a x : '0 ⊑ x -> a <= 1 -> a *: x ⊑ x.
Proof. by move=> hy hx; rewrite -{2}[x]scale1r lev_wpscale2r. Qed.

Lemma lev_niscale a x : x ⊑ 0 -> a <= 1 -> x ⊑ a *: x.
Proof. by move=> hy hx; rewrite -{1}[x]scale1r lev_wnscale2r. Qed.

End VOrderFieldTheory.

Section CanVOrderTheory.
Variable (R: numFieldType) (T : canVOrderType R).
Implicit Type (x y z : T) (a b c : R).
Local Notation "'0" := (0 : T).

Lemma pscalev_lgt0 y a : '0 ⊏ y -> ('0 ⊏ a *: y) = (0 < a).
Proof.
by move=>Py; rewrite !lt_def scaler_eq0 negb_or pscalev_lge0// lt0v_neq0// andbT.
Qed.

Lemma lev_pscale2r x : '0 ⊏ x -> {mono *:%R^~ x : x y / (x <= y)%O}.
Proof.
by move=>Px a b; rewrite -subv_ge0 -scalerBl pscalev_lge0// subr_ge0.
Qed.  

Lemma ltv_pscale2r x : '0 ⊏ x -> {mono *:%R^~ x : x y / (x < y)%O}.
Proof. by move=> x_gt0; apply: leW_mono (lev_pscale2r _). Qed.

Definition ltev_pscale2r := (lev_pscale2r, ltv_pscale2r).


Lemma lev_nscale2r x : x ⊏ 0 -> {mono *:%R^~ x : x y /~ (x <= y)%O}.
Proof.
by move=> x_lt0 y z /=; rewrite -levN2 -!scalerN lev_pscale2r// oppv_gt0.
Qed.

Lemma ltv_nscale2r x : x ⊏ 0 -> {mono *:%R^~ x : x y /~ (x < y)%O}.
Proof. by move=> x_lt0; apply: leW_nmono (lev_nscale2r _). Qed.

Definition ltev_nscale2r := (lev_nscale2r, ltv_nscale2r).

(* x positive and y left *)
Lemma pscalev_llt0 x a : '0 ⊏ x -> (a *: x ⊏ 0) = (a < 0).
Proof. by move=> x_gt0; rewrite -!oppv_gt0 -scaleNr pscalev_lgt0 // oppr_gt0. Qed.

Lemma pscalev_lle0 x a : '0 ⊏ x -> (a *: x ⊑ 0) = (a <= 0).
Proof. by move=> x_gt0; rewrite -!oppv_ge0 -scaleNr pscalev_lge0 // oppr_ge0. Qed.

(* x negative and y left *)
Lemma nscalev_lgt0 x a : x ⊏ 0 -> ('0 ⊏ a *: x) = (a < 0).
Proof. by move=> x_lt0; rewrite -scalerNN pscalev_lgt0 ?ltevNE// lterNE. Qed.

Lemma nscalev_lge0 x a : x ⊏ 0 -> ('0 ⊑ a *: x) = (a <= 0).
Proof. by move=> x_lt0; rewrite -scalerNN pscalev_lge0 ?ltevNE// lterNE. Qed.

Lemma nscalev_llt0 x a : x ⊏ 0 -> (a *: x ⊏ 0) = (0 < a).
Proof. by move=> x_lt0; rewrite -scalerNN pscalev_llt0 ?ltevNE// lterNE. Qed.

Lemma nscalev_lle0 x a : x ⊏ 0 -> (a *: x ⊑ 0) = (0 <= a).
Proof. by move=> x_lt0; rewrite -scalerNN pscalev_lle0 ?ltevNE// lterNE. Qed.

(* lev/ltv and multiplication between a positive/negative *)

Lemma gev_pscale a x : '0 ⊏ x -> (a *: x ⊑ x) = (a <= 1).
Proof. by move=> hy; rewrite -{2}[x]scale1r lev_pscale2r. Qed.

Lemma gtv_pscale a x : '0 ⊏ x -> (a *: x ⊏ x) = (a < 1).
Proof. by move=> hy; rewrite -{2}[x]scale1r ltv_pscale2r. Qed.

Lemma lev_pscale a x : '0 ⊏ x -> (x ⊑ a *: x) = (1 <= a).
Proof. by move=> hy; rewrite -{1}[x]scale1r lev_pscale2r. Qed.

Lemma ltv_pscale a x : '0 ⊏ x -> (x ⊏ a *: x) = (1 < a).
Proof. by move=> hy; rewrite -{1}[x]scale1r ltv_pscale2r. Qed.

Lemma gev_nscale a x : x ⊏ 0 -> (a *: x ⊑ x) = (1 <= a).
Proof. by move=> hy; rewrite -{2}[x]scale1r lev_nscale2r. Qed.

Lemma gtv_nscale a x : x ⊏ 0 -> (a *: x ⊏ x) = (1 < a).
Proof. by move=> hy; rewrite -{2}[x]scale1r ltv_nscale2r. Qed.

Lemma lev_nscale a x : x ⊏ 0 -> (x ⊑ a *: x) = (a <= 1).
Proof. by move=> hy; rewrite -{1}[x]scale1r lev_nscale2r. Qed.

Lemma ltv_nscale a x : x ⊏ 0 -> (x ⊏ a *: x) = (a < 1).
Proof. by move=> hy; rewrite -{1}[x]scale1r ltv_nscale2r. Qed.

End CanVOrderTheory.

Definition applyar_head U V W t (f : U -> V -> W) u v := let: tt := t in f v u.
Notation applyar := (@applyar_head _ _ _ tt).

HB.mixin Record isBRegVOrder
 (R: numFieldType) (U V W : vorderType R) (op : U -> V -> W) := {
  badditivel_subproof : forall u', additive (op^~ u');
  badditiver_subproof : forall u, additive (op u);
  bregv_eq0 : forall x y, op x y == 0 = (x == 0) || (y == 0);
  pbregv_rge0 : forall x y, (0 : U) ⊏ x -> ((0 : W) ⊑ op x y) = ((0 : V) ⊑ y);
  pbregv_lge0 : forall y x, (0 : V) ⊏ y -> ((0 : W) ⊑ op x y) = ((0 : U) ⊑ x);
}.

#[short(type="bregVOrder")]
HB.structure Definition BRegVOrder (R: numFieldType) (U V W : vorderType R) :=
  { f of isBRegVOrder R U V W f}.

Module BRegVOrderExports.
(* Module BRegVOrder.
Definition map (R: numFieldType) (U V W : vorderType R)
    (phUVW : phant (U -> V -> W)) := BRegVOrder.type U V W.
End BRegVOrder. *)
Notation "{ 'bregVOrder' U '->' V '->' W }" := (bregVOrder U%type V%type W%type)
  (at level 0, U at level 97, V at level 98, W at level 99, 
   format "{ 'bregVOrder'  U  ->  V  ->  W }") : ring_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use BRegVOrder.clone instead.")]
Notation "[ 'bregVOrder' 'of' f 'as' g ]" := (BRegVOrder.clone _ _ _ _ f g)
  (at level 0, format "[ 'bregVOrder'  'of'  f  'as'  g ]") : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use BRegVOrder.clone instead.")]
Notation "[ 'bregVOrder' 'of' f ]" := (BRegVOrder.clone _ _ _ _ f _)
  (at level 0, format "[ 'bregVOrder'  'of'  f ]") : form_scope.
End BRegVOrderExports.
HB.export BRegVOrderExports.

Section BRegVOrderTheory.
Variable (R: numFieldType) (U V W : vorderType R) (f : {bregVOrder U -> V -> W}).
Implicit Type (a b c : U) (x y z : V).

#[non_forgetful_inheritance]
HB.instance Definition _ a :=
  GRing.isAdditive.Build _ _ (f a) (@badditiver_subproof R U V W f a).
#[non_forgetful_inheritance]
HB.instance Definition _ z :=
  GRing.isAdditive.Build _ _ (applyar f z) (@badditivel_subproof R U V W f z).

Local Notation l0 := (0 : U).
Local Notation r0 := (0 : V).
Local Notation b0 := (0 : W).

(* it is additive, additiver *)
Lemma applyarE x : applyar f x =1 f^~ x. Proof. by []. Qed.

Lemma bregv0r a : f a 0 = 0. Proof. by rewrite raddf0. Qed.
Lemma bregvNr a : {morph f a : x / - x}. Proof. exact: raddfN. Qed.
Lemma bregvDr a : {morph f a : x y / x + y}. Proof. exact: raddfD. Qed.
Lemma bregvBr a : {morph f a : x y / x - y}. Proof. exact: raddfB. Qed.
Lemma bregvMnr a n : {morph f a : x / x *+ n}. Proof. exact: raddfMn. Qed.
Lemma bregvMNnr a n : {morph f a : x / x *- n}. Proof. exact: raddfMNn. Qed.
Lemma bregv_sumr a I r (P : pred I) E :
  f a (\sum_(i <- r | P i) E i) = \sum_(i <- r | P i) f a (E i).
Proof. exact: raddf_sum. Qed.
Lemma bregv0l x : f 0 x = 0. Proof. by rewrite -applyarE raddf0. Qed.
Lemma bregvNl x : {morph f^~ x : x / - x}.
Proof. by move=> ?; rewrite -applyarE raddfN. Qed.
Lemma bregvDl x : {morph f^~ x : x y / x + y}.
Proof. by move=> ??; rewrite -applyarE raddfD. Qed.
Lemma bregvBl x : {morph f^~ x : x y / x - y}.
Proof. by move=> ??; rewrite -applyarE raddfB. Qed.
Lemma bregvMnl x n : {morph f^~ x : x / x *+ n}.
Proof. by move=> ?; rewrite -applyarE raddfMn. Qed.
Lemma bregvMNnl x n : {morph f^~ x : x / x *- n}.
Proof. by move=> ?; rewrite -applyarE raddfMNn. Qed.
Lemma bregv_suml x I r (P : pred I) E :
  f (\sum_(i <- r | P i) E i) x = \sum_(i <- r | P i) f (E i) x.
Proof. by rewrite -applyarE raddf_sum. Qed.
Lemma bregvNN a x : f (-a) (-x) = f a x.
Proof. by rewrite bregvNl bregvNr opprK. Qed.

Lemma pbregv_rgt0 a x : l0 ⊏ a -> (b0 ⊏ f a x) = (r0 ⊏ x).
Proof.
move=>xgt0. rewrite !lt0v (pbregv_rge0 _ _ xgt0) bregv_eq0//.
by move: xgt0; rewrite lt_def=>/andP[/negPf->].
Qed.

Lemma pbregv_lgt0 x a : r0 ⊏ x -> (b0 ⊏ f a x) = (l0 ⊏ a).
Proof.
move=>xgt0. rewrite !lt0v (pbregv_lge0 _ _ xgt0) bregv_eq0//.
by move: xgt0; rewrite lt_def orbC=>/andP[/negPf->].
Qed.

Lemma bregvI_eq0 a x : a != 0 -> (f a x == 0) = (x == 0).
Proof. by rewrite bregv_eq0; move=>/negPf->. Qed.

Lemma bregvI a : a != 0 -> injective (f a).
Proof. by move=>Pa x y /eqP; rewrite -subr_eq0 -bregvBr/= bregvI_eq0// subr_eq0=>/eqP. Qed.

Lemma bregIv_eq0 x a : x != 0 -> (f a x == 0) = (a == 0).
Proof. by rewrite bregv_eq0 orbC; move=>/negPf->. Qed.

Lemma bregIv x : x != 0 -> injective (f^~ x).
Proof. by move=>Px a y /eqP; rewrite -subr_eq0 -bregvBl/= bregIv_eq0// subr_eq0=>/eqP. Qed.

Lemma lev_pbreg2lP a x y : l0 ⊏ a -> x ⊑ y -> (f a x) ⊑ (f a y).
Proof. by move=>Pa Pxy; rewrite -subv_ge0 -bregvBr/= pbregv_rge0// subv_ge0. Qed.

(* mulr and lev/ltv *)
Lemma lev_pbreg2l a : l0 ⊏ a -> {mono (f a) : x y / x ⊑ y}.
Proof.
by move=> x_gt0 y z /=; rewrite -subv_ge0 -bregvBr pbregv_rge0// subv_ge0.
Qed.

Lemma ltv_pbreg2l a : l0 ⊏ a -> {mono (f a) : x y / x ⊏ y}.
Proof. by move=> x_gt0; apply: leW_mono (lev_pbreg2l _). Qed.

Definition ltev_pbreg2l := (lev_pbreg2l, ltv_pbreg2l).

Lemma lev_pbreg2r x : r0 ⊏ x -> {mono f^~ x : x y / x ⊑ y}.
Proof.
by move=> x_gt0 y z /=; rewrite -subv_ge0 -bregvBl pbregv_lge0// subv_ge0.
Qed.  

Lemma ltv_pbreg2r x : r0 ⊏ x -> {mono f^~ x : x y / x ⊏ y}.
Proof. by move=> x_gt0; apply: leW_mono (lev_pbreg2r _). Qed.

Definition ltev_pbreg2r := (lev_pbreg2r, ltv_pbreg2r).

Lemma lev_nbreg2l a : a ⊏ 0 -> {mono (f a) : x y /~ x ⊑ y}.
Proof.
by move=> x_lt0 y z /=; rewrite -levN2 -!bregvNl/= lev_pbreg2l ?oppv_gt0.
Qed.

Lemma ltv_nbreg2l a : a ⊏ 0 -> {mono (f a) : x y /~ x ⊏ y}.
Proof. by move=> x_lt0; apply: leW_nmono (lev_nbreg2l _). Qed.

Definition ltev_nbreg2l := (lev_nbreg2l, ltv_nbreg2l).

Lemma lev_nbreg2r x : x ⊏ 0 -> {mono f^~ x : x y /~ x ⊑ y}.
Proof.
by move=> x_lt0 y z /=; rewrite -levN2 -!bregvNr lev_pbreg2r// oppv_gt0.
Qed.

Lemma ltv_nbreg2r x : x ⊏ 0 -> {mono f^~ x : x y /~ x ⊏ y}.
Proof. by move=> x_lt0; apply: leW_nmono (lev_nbreg2r _). Qed.

Definition ltev_nbreg2r := (lev_nbreg2r, ltv_nbreg2r).

Lemma lev_wpbreg2l a : l0 ⊑ a -> {homo (f a) : y z / y ⊑ z}.
Proof.
by rewrite le0v => /orP[/eqP-> y z | /lev_pbreg2l/mono2W//]; rewrite !bregv0l.
Qed.

Lemma lev_wnbreg2l a : a ⊑ 0 -> {homo (f a) : y z /~ y ⊑ z}.
Proof.
by move=> x_le0 y z leyz; rewrite -![f a _]bregvNN lev_wpbreg2l ?ltevNE.
Qed.

Lemma lev_wpbreg2r x : r0 ⊑ x -> {homo f^~ x : y z / y ⊑ z}.
Proof.
by rewrite le0v => /orP[/eqP-> y z | /lev_pbreg2r/mono2W//]; rewrite !bregv0r.
Qed.

Lemma lev_wnbreg2r x : x ⊑ 0 -> {homo f^~ x : y z /~ y ⊑ z}.
Proof.
by move=> x_le0 y z leyz; rewrite -![f _ x]bregvNN lev_wpbreg2r ?ltevNE.
Qed.

(* Binary forms, for backchaining. *)
Lemma lev_pbreg2 a b x y :
  l0 ⊑ a -> r0 ⊑ x -> a ⊑ b -> x ⊑ y -> f a x ⊑ f b y.
Proof.
move=> x1ge0 x2ge0 le_xy1 le_xy2; have y1ge0 := le_trans x1ge0 le_xy1.
exact: le_trans (lev_wpbreg2r x2ge0 le_xy1) (lev_wpbreg2l y1ge0 le_xy2).
Qed.

Lemma ltv_pbreg2 a b x y :
  l0 ⊑ a -> r0 ⊑ x -> a ⊏ b -> x ⊏ y -> f a x ⊏ f b y.
Proof.
move=> x1ge0 x2ge0 lt_xy1 lt_xy2; have y1gt0 := le_lt_trans x1ge0 lt_xy1.
by rewrite (le_lt_trans (lev_wpbreg2r x2ge0 (ltW lt_xy1))) ?ltv_pbreg2l.
Qed.

Lemma pbregv_rlt0 a x : l0 ⊏ a -> (f a x ⊏ 0) = (x ⊏ 0).
Proof. by move=> x_gt0; rewrite -!oppv_gt0 -bregvNr pbregv_rgt0// oppv_gt0. Qed.

Lemma pbregv_rle0 a x : l0 ⊏ a -> (f a x ⊑ 0) = (x ⊑ 0).
Proof. by move=> x_gt0; rewrite -!oppv_ge0 -bregvNr pbregv_rge0// oppr_ge0. Qed.

Lemma nbregv_rgt0 a x : a ⊏ 0 -> (b0 ⊏ f a x) = (x ⊏ 0).
Proof. by move=> x_lt0; rewrite -bregvNN pbregv_rgt0 ?ltevNE. Qed.

Lemma nbregv_rge0 a x : a ⊏ 0 -> (b0 ⊑ f a x) = (x ⊑ 0).
Proof. by move=> x_lt0; rewrite -bregvNN pbregv_rge0 ?ltevNE. Qed.

Lemma nbregv_rlt0 a x : a ⊏ 0 -> (f a x ⊏ 0) = (r0 ⊏ x).
Proof. by move=> x_lt0; rewrite -bregvNN pbregv_rlt0 ?ltevNE. Qed.

Lemma nbregv_rle0 a x : a ⊏ 0 -> (f a x ⊑ 0) = (r0 ⊑ x).
Proof. by move=> x_lt0; rewrite -bregvNN pbregv_rle0 ?ltevNE. Qed.

Lemma pbregv_llt0 x a : r0 ⊏ x -> (f a x ⊏ 0) = (a ⊏ 0).
Proof. by move=> x_gt0; rewrite -!oppv_gt0 -bregvNl pbregv_lgt0// oppv_gt0. Qed.

Lemma pbregv_lle0 x a : r0 ⊏ x -> (f a x ⊑ 0) = (a ⊑ 0).
Proof. by move=> x_gt0; rewrite -!oppv_ge0 -bregvNl pbregv_lge0// oppr_ge0. Qed.

Lemma nbregv_lgt0 x a : x ⊏ 0 -> (b0 ⊏ f a x) = (a ⊏ 0).
Proof. by move=> x_lt0; rewrite -bregvNN pbregv_lgt0 ?ltevNE. Qed.

Lemma nbregv_lge0 x a : x ⊏ 0 -> (b0 ⊑ f a x) = (a ⊑ 0).
Proof. by move=> x_lt0; rewrite -bregvNN pbregv_lge0 ?ltevNE. Qed.

Lemma nbregv_llt0 x a : x ⊏ 0 -> (f a x ⊏ 0) = (l0 ⊏ a).
Proof. by move=> x_lt0; rewrite -bregvNN pbregv_llt0 ?ltevNE. Qed.

Lemma nbregv_lle0 x a : x ⊏ 0 -> (f a x ⊑ 0) = (l0 ⊑ a).
Proof. by move=> x_lt0; rewrite -bregvNN pbregv_lle0 ?ltevNE. Qed.

(* weak and symmetric lemmas *)
Lemma bregv_ge0 a x : l0 ⊑ a -> r0 ⊑ x -> b0 ⊑ f a x.
Proof. by move=> x_ge0 y_ge0; rewrite -(bregv0r a) lev_wpbreg2l. Qed.

Lemma bregv_le0 a x : a ⊑ 0 -> x ⊑ 0 -> b0 ⊑ f a x.
Proof. by move=> x_le0 y_le0; rewrite -(bregv0r a) lev_wnbreg2l. Qed.

Lemma bregv_ge0_le0 a x : l0 ⊑ a -> x ⊑ 0 -> f a x ⊑ 0.
Proof. by move=> x_le0 y_le0; rewrite -(bregv0r a) lev_wpbreg2l. Qed.

Lemma bregv_le0_ge0 a x : a ⊑ 0 -> r0 ⊑ x -> f a x ⊑ 0.
Proof. by move=> x_le0 y_le0; rewrite -(bregv0r a) lev_wnbreg2l. Qed.

(* bregv_gt0 with only one case *)

Lemma bregv_gt0 a x : l0 ⊏ a -> r0 ⊏ x -> b0 ⊏ f a x.
Proof. by move=> x_gt0 y_gt0; rewrite pbregv_rgt0. Qed.

Lemma bregv_lt0 a x : a ⊏ 0 -> x ⊏ 0 -> b0 ⊏ f a x.
Proof. by move=> x_le0 y_le0; rewrite nbregv_rgt0. Qed.

Lemma bregv_gt0_lt0 a x : l0 ⊏ a -> x ⊏ 0 -> f a x ⊏ 0.
Proof. by move=> x_le0 y_le0; rewrite pbregv_rlt0. Qed.

Lemma bregv_lt0_gt0 a x : a ⊏ 0 -> r0 ⊏ x -> f a x ⊏ 0.
Proof. by move=> x_le0 y_le0; rewrite nbregv_rlt0. Qed.

End BRegVOrderTheory.

(* for singular value decomposition. operations on diagnal elements, 
  such as p-norm of vectors. Schatten norms. Ky Fan norm.*)
Section MatrixDotOperator.
Variable (R: numClosedFieldType).

Fact dmulmx_key : unit. Proof. by []. Qed.
Definition dmulmx {m n} (A B : 'M[R]_(m,n)) := 
    \matrix[dmulmx_key]_(i,j) (A i j * B i j).
Notation "A .* B" := (dmulmx A B) 
  (at level 40, left associativity, format "A  .*  B").

Lemma dmulmxC m n (A B : 'M[R]_(m,n)) : A .* B = B .* A.
Proof. by apply/matrixP=>i j; rewrite !mxE mulrC. Qed.

Lemma dmulmxA m n (A B C: 'M[R]_(m,n)) : A .* (B .* C) = A .* B .* C.
Proof. by apply/matrixP=>i j; rewrite !mxE mulrA. Qed.

Lemma dmulmxDl m n (A B C: 'M[R]_(m,n)) :
  (A + B) .* C = A .* C + B .* C.
Proof. by apply/matrixP=>i j; rewrite !mxE mulrDl. Qed.

Lemma dmulmxDr m n (A B C: 'M[R]_(m,n)) :
  A .* (B + C) = A .* B + A .* C.
Proof. by apply/matrixP=>i j; rewrite !mxE mulrDr. Qed.

Definition dexpmx {m n} (A : 'M[R]_(m,n)) k := map_mx ((@GRing.exp R) ^~ k) A.
Notation "A .^+ n" := (dexpmx A n) (at level 29, n at next level) : ring_scope.
Notation "A .^-1" := (map_mx ((@GRing.inv R)) A) (at level 3) : ring_scope.
Notation "A .^- n" := ((dexpmx A n).^-1) (at level 29, n at next level) : ring_scope.

Lemma dexpmx0 m n (A: 'M[R]_(m,n)) : A .^+ 0 = const_mx 1.
Proof. by apply/matrixP=>i j; rewrite !mxE expr0. Qed.

Lemma dexpmx1 m n (A: 'M[R]_(m,n)) : A .^+ 1 = A.
Proof. by apply/matrixP=>i j; rewrite !mxE expr1. Qed.

Lemma dexpmx2 m n (A: 'M[R]_(m,n)) : A .^+ 2 = dmulmx A A.
Proof. by apply/matrixP=>i j; rewrite !mxE expr2. Qed.

Lemma dexpmxS m n (A: 'M[R]_(m,n)) k : A .^+ k.+1 = A .* (A .^+ k).
Proof. by apply/matrixP=>i j; rewrite !mxE exprS. Qed.

Lemma dexpmx0n m n k : (0 : 'M[R]_(m,n)) .^+ k = const_mx (k == 0%N)%:R.
Proof. by apply/matrixP=>i j; rewrite !mxE expr0n. Qed.

Lemma dexpmx1n m n k : (const_mx 1 : 'M[R]_(m,n)) .^+ k = const_mx 1.
Proof. by apply/matrixP=>i j; rewrite !mxE expr1n. Qed.

Lemma dexpmxD m n (A: 'M[R]_(m,n)) p q : A .^+ (p + q) = A .^+ p .* A .^+ q.
Proof. by apply/matrixP=>i j; rewrite !mxE exprD. Qed.

Lemma dexpmxSr m n (A: 'M[R]_(m,n)) k : A .^+ k.+1 = A .^+ k .* A.
Proof. by apply/matrixP=>i j; rewrite !mxE exprSr. Qed.

Lemma dexprm_inj m n k : (0 < k)%N -> {in nnegmx &, injective (@dexpmx m n ^~ k)}.
Proof.
move=>kgt0 A B AR BR /matrixP De; apply/matrixP=>i j.
move: (De i j)=>/eqP; rewrite /dexpmx !mxE eqrXn2//.
1,2: by apply/nnegmxP. by move=>/eqP.
Qed.

Definition dmxortho {m n} (A : 'M[R]_(m,n)) := const_mx 1 - (A .* (A .^-1)) .

Lemma dmxorthoE {m n} (A : 'M[R]_(m,n)) : 
  dmxortho A = const_mx 1 - (A .* (A .^-1)) .
Proof. by []. Qed.

Lemma dmxorthoC {m n} (A : 'M[R]_(m,n)) : 
  (A .* (A .^-1)) + dmxortho A = const_mx 1.
Proof. by rewrite /dmxortho addrC addrNK. Qed.

Lemma dmxortho_elem {m n} (A : 'M[R]_(m,n)) i j :
 (dmxortho A) i j = (A i j == 0)%:R.
Proof.
rewrite /dmxortho !mxE; case P: (A i j == 0).
by move/eqP: P=>->; rewrite mul0r subr0.
by rewrite mulfV ?P// subrr.
Qed.

Lemma dmxorthoP {m n} (A : 'M[R]_(m,n)) : A .* (dmxortho A) = 0.
Proof.
apply/matrixP=>i j; rewrite mxE dmxortho_elem !mxE.
by case P: (A i j == 0); [move/eqP: P=>->|]; rewrite ?mul0r ?mulr0.
Qed.

Lemma dmxortho_adj {m n} (A : 'M[R]_(m,n)) : (dmxortho A) ^*m = (dmxortho A).
Proof. by apply/matrixP=>i j; rewrite mxE !dmxortho_elem conjC_nat. Qed.

Lemma dmxortho_dexp {m n} (A : 'M[R]_(m,n)) k : 
  (0 < k)%N -> dmxortho (A .^+ k) = dmxortho A.
Proof. by move=>P; apply/matrixP=>i j; rewrite !dmxortho_elem !mxE expf_eq0 P. Qed.

Lemma dmxortho_inv {m n} (A : 'M[R]_(m,n)) : dmxortho (A .^-1) = dmxortho A.
Proof. by apply/matrixP=>i j; rewrite !dmxortho_elem !mxE invr_eq0. Qed.

Lemma dmxortho_invn {m n} (A : 'M[R]_(m,n)) k : 
  (0 < k)%N -> dmxortho (A .^-k) = dmxortho A.
Proof. rewrite dmxortho_inv; exact: dmxortho_dexp. Qed.

Lemma diag_mx_adj n (A : 'rV[R]_n) : (diag_mx A)^*t = diag_mx (A ^*m).
Proof. 
apply/matrixP=>i j; rewrite !mxE eq_sym. 
by case: eqP=>[->|_]; rewrite ?mulr1n ?mulr0n ?conjC0.
Qed.

Lemma diag_mx_dmul n (A B : 'rV[R]_n) : 
  diag_mx A *m diag_mx B = diag_mx (dmulmx A B).
Proof.
apply/matrixP=>i j; rewrite !mxE (bigD1 i)// big1/= ?mxE.
by move=>k /negPf nki; rewrite !mxE eq_sym nki mulr0n mul0r.
by case E: (i == j); rewrite ?eqxx ?mulr1n ?mulr0n ?addr0 ?mulr0.
Qed.

Lemma expmx_diag n (A: 'rV[R]_n.+1) k : (diag_mx A) ^+ k = diag_mx (A .^+ k).
Proof. 
elim: k=>[|k IH]; first by rewrite expr0 dexpmx0 diag_const_mx.
by rewrite exprS IH /GRing.mul/= diag_mx_dmul dexpmxS.
Qed.

Definition dnthrootmx k {m n} (A: 'M[R]_(m, n)) := map_mx (@nthroot R k) A.

Lemma dmxortho_root {m n} (A : 'M[R]_(m,n)) k : 
  (0 < k)%N -> dmxortho (dnthrootmx k A) = dmxortho A.
Proof. by move=>P; apply/matrixP=>i j; rewrite !dmxortho_elem !mxE rootC_eq0. Qed.

Lemma diag_mx_inj n : injective (@diag_mx R n).
Proof.
move=>u v /matrixP P; apply/matrixP=>i j.
by move: (P j j); rewrite !mxE !eqxx !mulr1n !ord1.
Qed.

Lemma mulUmx m n (U : 'M[R]_m) (A B : 'M[R]_(m,n)) : 
  U \is unitarymx -> U *m A = B <-> A = U ^*t *m B.
Proof.
move=>P; move: P {+}P=>/unitarymxP P1 /unitarymxPV P2.
by split=>[ <-|->]; rewrite mulmxA ?P1 ?P2 mul1mx.
Qed.

Lemma mulUCmx m n (U : 'M[R]_m) (A B : 'M[R]_(m,n)) : 
  U \is unitarymx -> U ^*t *m A = B <-> A = U *m B.
Proof. 
move=>P; move: P {+}P=>/unitarymxP P1 /unitarymxPV P2.
by split=>[ <-|->]; rewrite mulmxA ?P1 ?P2 mul1mx.
Qed.

Lemma mulmxU m n (U : 'M[R]_n) (A B : 'M[R]_(m,n)) :
  U \is unitarymx -> A *m U = B <-> A = B *m U ^*t.
Proof.
move=>P; move: P {+}P=>/unitarymxP P1 /unitarymxPV P2.
by split=>[ <-|->]; rewrite -mulmxA ?P1 ?P2 mulmx1.
Qed.

Lemma mulmxUC m n (U : 'M[R]_n) (A B : 'M[R]_(m,n)) :
  U \is unitarymx -> A *m U ^*t = B <-> A = B *m U.
Proof.
move=>P; move: P {+}P=>/unitarymxP P1 /unitarymxPV P2.
by split=>[ <-|->]; rewrite -mulmxA ?P1 ?P2 mulmx1.
Qed.

Lemma unitarymxK m n  (U : 'M[R]_(m,n)) : U \is unitarymx -> U *m U ^*t = 1%:M.
Proof. by move/unitarymxP. Qed.

Lemma unitarymxKV m  (U : 'M[R]_m) : U \is unitarymx -> U ^*t *m U = 1%:M.
Proof. by move/unitarymxPV. Qed.

Lemma adjmx_const m a : (a%:M : 'M[R]_m) ^*t = (a^*)%:M.
Proof.
apply/matrixP=>i j; rewrite !mxE eq_sym.
by case: eqP=>_; rewrite ?mulr1n// !mulr0n conjC0.
Qed.

Lemma normalmx_const m (a : R) : (a%:M : 'M[R]_m) \is normalmx.
Proof. 
by apply/normalmxP; rewrite -scalemx1 -!(scalemxAr,scalemxAl) -adjmxE
  adjmxZ -!(scalemxAl,scalemxAr) mulmx1 mul1mx.
Qed.

Lemma spectral_diag_const n (a : R) : spectral_diag (a%:M : 'M[R]_n) = const_mx a.
Proof.
move: (normalmx_const n a)=>/eigen_dec/esym.
by rewrite mulmxUC// mulUmx// -{3}scalemx1 -scalemxAl mul1mx 
  -scalemxAr unitarymxKV// scalemx1 -{2}diag_const_mx=>/diag_mx_inj.
Qed.

Lemma spectral_diag0 n : spectral_diag (0 : 'M[R]_n) = 0.
Proof. by rewrite -scalemx0 spectral_diag_const const_mx0. Qed.

Lemma spectral_diag1 n : spectral_diag (1%:M : 'M[R]_n) = const_mx 1.
Proof. exact: spectral_diag_const. Qed.

Lemma unitarymx1 n : (1%:M : 'M[R]_n) \is unitarymx.
Proof. by apply/unitarymxP; rewrite mul1mx -adjmxE adjmx_const conjC1. Qed.

Lemma unitarymxZ n a (A : 'M[R]_n) : 
  `|a| = 1 -> A \is unitarymx -> (a *: A) \is unitarymx.
Proof.
move=>P1 /unitarymxP P2; apply/unitarymxP.
by rewrite -adjmxE adjmxZ -scalemxAr -scalemxAl scalerA P2 -normCKC P1 expr1n scale1r.
Qed.

Lemma unitarymxZ_diag n (D : 'rV[R]_n) (A : 'M[R]_n) : (forall i, `|D 0 i| = 1) 
  -> A \is unitarymx -> (diag_mx D *m A) \is unitarymx.
Proof.
move=>P1 P2; apply/unitarymxPV; rewrite adjmxM !mulmxA mulmxU// -mulmxA mulUCmx// 
  mul1mx [RHS]unitarymxK// diag_mx_adj diag_mx_dmul -diag_const_mx.
by f_equal; apply/matrixP=>i j; rewrite !mxE ord1 -normCKC P1 expr1n.
Qed.

End MatrixDotOperator.

Notation "A .* B" := (dmulmx A B) (at level 40, left associativity, format "A  .*  B").
Notation "A .^+ n" := (dexpmx A n) (at level 29, n at next level) : ring_scope.
Notation "A .^-1" := (map_mx ((@GRing.inv _)) A) (at level 3) : ring_scope.
Notation "A .^- n" := ((dexpmx A n).^-1) (at level 29, n at next level) : ring_scope.
Notation "n .-rootdmx" := (dnthrootmx n) (at level 2, format "n .-rootdmx") : ring_scope.
Notation "A ._|_" := (dmxortho A) (at level 3) : ring_scope.
Notation sqrtdmx := (dnthrootmx 2).

(* entry wise p norm *)
Section PNorm.
Variable (R: numClosedFieldType) (p' m n: nat).
Implicit Type (A B : 'M[R]_(m,n)).
Local Notation p := (p'.+1).

Definition pnorm A := p.-root (\sum_i `|A i.1 i.2| ^+ p).

Lemma pnorm_pair A : pnorm A = p.-root (\sum_i\sum_j (`|A i j| ^+p)).
Proof. by rewrite /pnorm; f_equal; rewrite pair_bigA. Qed.

Lemma pnorm0_eq0 : forall A, pnorm A = 0 -> A = 0.
Proof.
move=>A /eqP; rewrite /pnorm rootC_eq0// =>/eqP.
have P1 i: true -> 0 <= `|A i.1 i.2| ^+ p by move=>_; apply/exprn_ge0/normr_ge0.
move/(psumr_eq0P P1)=>P2; apply/matrixP=>i j; move: (P2 (i,j) isT)=>/eqP.
by rewrite mxE expf_eq0/= normr_eq0=>/eqP.
Qed.

Lemma pnorm_ge0 : forall A, pnorm A >= 0.
Proof.
move=>A; rewrite /pnorm rootC_ge0//.
by apply sumr_ge0=>i _; apply exprn_ge0.
Qed.

Lemma pnorm_nneg A : pnorm A \is Num.nneg.
Proof. by rewrite qualifE /Rnneg_pred pnorm_ge0. Qed.

Lemma pnormZ a A : pnorm (a *: A) = `|a| * pnorm A.
Proof.
rewrite -(rootCK (ltn0Sn p') `|a|) /pnorm -rootCX// -rootCMl ?exprn_ge0//.
f_equal; rewrite mulr_sumr; apply eq_bigr=>i _.
by rewrite !mxE normrM exprMn.
Qed.

Lemma pnorm0 : pnorm 0 = 0.
Proof. by rewrite -(scale0r 0) pnormZ normr0 mul0r. Qed.

Lemma pnorm0P A : reflect (pnorm A = 0) (A == 0).
Proof. by apply: (iffP eqP)=> [->|/pnorm0_eq0 //]; apply: pnorm0. Qed.

Definition pnorm_eq0 A := sameP (pnorm A =P 0) (pnorm0P A).

Lemma pnorm_triangle A B : pnorm (A + B) <= pnorm A + pnorm B.
Proof.
rewrite/pnorm; under eq_bigr do rewrite mxE.
apply: discrete_Minkowski_inequality.
Qed.

HB.instance Definition _ := isVNorm.Build R 'M_(m, n) pnorm
  pnorm_triangle pnorm0_eq0 pnormZ.

End PNorm.

Definition l1norm (R: numClosedFieldType) (m n: nat) := (@pnorm R 0 m n).
Definition l2norm (R: numClosedFieldType) (m n: nat) := (@pnorm R 1 m n).

Section L1L2Norm.
Variable (R: numClosedFieldType) (m n: nat).
Local Notation M := 'M[R]_(m,n).

Lemma pnorm_trmx p q r (M: 'M[R]_(q,r)) : pnorm p (M^T) = pnorm p M.
Proof.
rewrite !pnorm_pair; f_equal; rewrite exchange_big.
by under eq_bigr do under eq_bigr do rewrite mxE.
Qed.

Lemma pnorm_adjmx p q r (M: 'M[R]_(q,r)) : pnorm p (M^*t) = pnorm p M.
Proof. by rewrite -pnorm_trmx /pnorm; under eq_bigr do rewrite !mxE norm_conjC. Qed.

Lemma pnorm_conjmx p q r (M: 'M[R]_(q,r)) : pnorm p (M^*m) = pnorm p M.
Proof. by rewrite -pnorm_adjmx adjmxCT conjmxK pnorm_trmx. Qed.

Lemma pnorm_diag p q (D : 'rV[R]_q) : pnorm p (diag_mx D) = pnorm p D.
Proof.
rewrite !pnorm_pair big_ord1; f_equal; apply eq_bigr=>i _.
rewrite (bigD1 i)//= big1 ?mxE ?eqxx ?mulr1n ?addr0// =>j /negPf nji.
by rewrite mxE eq_sym nji mulr0n normr0 expr0n.
Qed.

Lemma l1norm_ge0 : forall (A : M), l1norm A >= 0. Proof. exact: pnorm_ge0. Qed.
Lemma l1norm_nneg (A : M) : l1norm A \is Num.nneg. Proof. exact: pnorm_nneg. Qed.
Lemma l2norm_ge0 : forall (A : M), l2norm A >= 0. Proof. exact: pnorm_ge0. Qed.
Lemma l2norm_nneg (A : M) : l2norm A \is Num.nneg. Proof. exact: pnorm_nneg. Qed.
Local Hint Resolve l1norm_nneg : core.
Local Hint Resolve l2norm_nneg : core.
Local Hint Resolve l1norm_ge0 : core.
Local Hint Resolve l2norm_ge0 : core.

Lemma l1norm_trmx (A : M) : l1norm (A^T) = l1norm A. Proof. exact: pnorm_trmx. Qed.
Lemma l1norm_adjmx (A : M) : l1norm (A^*t) = l1norm A. Proof. exact: pnorm_adjmx. Qed.
Lemma l1norm_conjmx (A : M) : l1norm (A^*m) = l1norm A. Proof. exact: pnorm_conjmx. Qed.
Lemma l1norm_diag (D : 'rV[R]_m) : l1norm (diag_mx D) = l1norm D. 
Proof. exact: pnorm_diag. Qed.
Lemma l2norm_trmx (A : M) : l2norm (A^T) = l2norm A. Proof. exact: pnorm_trmx. Qed.
Lemma l2norm_adjmx (A : M) : l2norm (A^*t) = l2norm A. Proof. exact: pnorm_adjmx. Qed.
Lemma l2norm_conjmx (A : M) : l2norm (A^*m) = l2norm A. Proof. exact: pnorm_conjmx. Qed.
Lemma l2norm_diag (D : 'rV[R]_m) : l2norm (diag_mx D) = l2norm D. 
Proof. exact: pnorm_diag. Qed.

Lemma dotV_l2norm (M: 'M[R]_(m,n)) : \tr (M ^*t *m M) = l2norm M ^+2.
Proof.
rewrite /l2norm sqrtCK -(pair_bigA _ (fun x y=> `|M x y| ^+2))/= exchange_big.
rewrite /mxtrace; apply eq_bigr=>i _; rewrite !mxE; apply eq_bigr=>j _.
by rewrite !mxE normCKC.
Qed.

Lemma dot_l2norm (M: 'M[R]_(m,n)) : \tr (M *m M ^*t) = l2norm M ^+2.
Proof. by rewrite -dotV_l2norm mxtrace_mulC. Qed.

Lemma l2norm_dotV (M: 'M[R]_(m,n)) : l2norm M = sqrtC (\tr (M ^*t *m M)).
Proof. by rewrite dotV_l2norm exprCK// pnorm_ge0. Qed.

Lemma l2norm_dot (M: 'M[R]_(m,n)) : l2norm M = sqrtC (\tr (M *m M ^*t)).
Proof. by rewrite l2norm_dotV mxtrace_mulC. Qed.

Lemma l1normE (A : 'M[R]_(m,n)) : l1norm A = \sum_i\sum_j `|A i j|.
Proof. rewrite /l1norm pnorm_pair root1C; do 2 apply/eq_bigr=>? _; apply expr1. Qed.

Lemma l1norm_triangle (A B : 'M[R]_(m,n)) : l1norm (A + B) <= l1norm A + l1norm B.
Proof. exact: pnorm_triangle. Qed.

Lemma l2norm_triangle (A B : 'M[R]_(m,n)) : l2norm (A + B) <= l2norm A + l2norm B.
Proof. exact: pnorm_triangle. Qed.

Lemma l2norm_l1norm (A: 'M[R]_(m,n)) : l2norm A <= l1norm A.
Proof.
rewrite -(ler_pXn2r (ltn0Sn 1)) ?pnorm_nneg// /l1norm /l2norm /pnorm 
  sqrtCK root1C [in X in _ <= X](eq_bigr (fun i=>`|A i.1 i.2|)).
by move=>i _; rewrite expr1. apply normr_sqr_ler_sum.
Qed.

Lemma l1norm_l2norm (A: 'M[R]_(m,n)) : l1norm A <= sqrtC (m * n)%:R * l2norm A.
Proof.
rewrite -(ler_pXn2r (ltn0Sn 1)) ?nnegrE ?mulr_ge0 ?pnorm_ge0// ?sqrtC_ge0 
  ?ler0n// exprMn /l1norm /l2norm /pnorm !sqrtCK root1C [in X in X <= _]
  (eq_bigr (fun i=>`|A i.1 i.2|)); first by move=>i _; rewrite expr1.
suff ->: (\sum_i `|A i.1 i.2|) = `| \sum_i ((fun=>1) i) * `|A i.1 i.2| |.
apply (le_trans (Cauchy_Schwarz_C _ _ _ _)).
rewrite sumr_const normr1 expr1n card_prod !card_ord.
by under eq_bigr do rewrite normr_id.
rewrite ger0_norm; first by apply sumr_ge0=>i _; rewrite mulr_ge0.
by apply eq_bigr=>i _; rewrite mul1r.
Qed.

Lemma l2normUl (U : 'M[R]_m) (M : 'M[R]_(m,n)): 
  U \is unitarymx -> l2norm (U *m M) = l2norm M.
Proof.
by move=>P; rewrite l2norm_dot !adjmxM -!mulmxA 
mxtrace_mulC mulmxA mulmxKtV// -l2norm_dot.
Qed.

Lemma l2normUr (U : 'M[R]_n) (M : 'M[R]_(m,n)): 
  U \is unitarymx -> l2norm (M *m U) = l2norm M.
Proof.
by move=>P; rewrite l2norm_dot !adjmxM !mulmxA mulmxtVK// -l2norm_dot.
Qed.

Lemma l2norm_deltamx i j : l2norm (delta_mx i j : 'M[R]_(m,n)) = 1.
Proof.
rewrite /l2norm pnorm_pair (bigD1 i)//= (bigD1 j)//= !big1.
1,2: move=>k /negPf nk. 2: rewrite big1// =>l _.
1,2: by rewrite mxE nk/= ?andbF normr0 expr0n.
by rewrite mxE !eqxx normr1 expr1n !addr0 sqrtC1.
Qed.

HB.instance Definition _ := isVNorm.Build R 'M_(m, n) (@l1norm R m n)
  l1norm_triangle (@pnorm0_eq0 _ 0 _ _) (@pnormZ _ 0 _ _).
HB.instance Definition _ := isVNorm.Build R 'M_(m, n) (@l2norm R m n)
  l2norm_triangle (@pnorm0_eq0 _ 1 _ _) (@pnormZ _ 1 _ _).

End L1L2Norm.

Section sort_real_vect.
Variable (R: numFieldType) (n: nat).
Implicit Type (v : 'rV[R]_n).

Definition is_decreasing :=
  [qualify v : 'rV[R]_n | 
    [forall i : 'I_n, 
      [forall j : 'I_n, (i > j)%N || (v 0 i >= v 0 j) ]]].

Lemma is_decreasingP (v : 'rV[R]_n) :
  reflect (forall i j : 'I_n, (i > j)%N || (v 0 i >= v 0 j)) 
    (v \is is_decreasing).
Proof.
apply/(iffP forallP)=>[H i j|H i]; last by apply/forallP.
by move: (H i)=>/forallP/(_ j).
Qed.

Notation PR := Num.real.
Notation geR := (fun x y : R => x >= y).

Lemma geR_total : {in PR &, total geR}.
Proof. move=>x y. rewrite orbC. exact: real_leVge. Qed.

Lemma geR_transitive : {in PR & &, transitive geR}.
Proof. move=>x y z _ _ _ P1 P2. apply (le_trans P2 P1). Qed.

Lemma geR_refl : {in PR, reflexive geR}.
Proof. by []. Qed.

Let s v := [tuple of [seq v 0 i | i <- ord_tuple n]].
Let ss v := sort geR (s v).

Lemma size_sort_s v : size (ss v) == n.
Proof. by rewrite size_sort size_tuple. Qed.

Definition tsort_s v := Tuple (size_sort_s v).

Lemma tsort_sE v : tsort_s v = ss v :> seq R.
Proof. by []. Qed.

Lemma all_geR_s v : v \is a realmx -> all (has_quality O PR) (s v).
Proof.
move=>/realmxP/(_ 0) Pr; apply/(all_tnthP)=>i.
rewrite tnth_map tnth_ord_tuple. by move: (Pr i).
Qed. 

Lemma all_geR_sort_s v : v \is a realmx -> all (has_quality O PR) (ss v).
Proof. by move=>Pr; rewrite all_sort all_geR_s. Qed.

Lemma sort_s_sorted v: v \is a realmx -> sorted geR (ss v).
Proof. by move=>Pr; apply: (sort_sorted_in geR_total (all_geR_s Pr)). Qed.

Lemma sort_tsort_perm v : perm_eq (s v) (tsort_s v).
Proof. by rewrite tsort_sE perm_sym perm_sort. Qed.

Lemma ltn_ordK m (i : 'I_m) : Ordinal (ltn_ord i) = i. 
Proof. by destruct i; rewrite (eq_irrelevance (ltn_ord (Ordinal i)) i). Qed.

Lemma perm_exists_sort_t v : exists p : 'S_n, 
  forall i : 'I_n, (s v)~_i = (tsort_s v)~_(p i).
Proof.
move: (sort_tsort_perm v)=>/tuple_permP=>[[p Pp]]; exists p=>i.
by rewrite (tnth_nth 0) Pp nth_tnth tnth_map tnth_ord_tuple ltn_ordK.
Qed.

Definition sort_v v := \matrix_(i < 1, j < n) (tsort_s v)~_j.

Lemma perm_sort_v v : exists p : 'S_n, col_perm p v = sort_v v.
Proof.
move: (perm_exists_sort_t v)=>[p Pp].
exists (invg p). apply/matrixP=>i j.
by rewrite !ord1 !mxE -{2}(permKV p j) -Pp tnth_map tnth_ord_tuple.
Qed.

Lemma homo_sort_s v (i j : 'I_n) : v \is a realmx -> 
  (i <= j)%N -> (tsort_s v)~_i >= (tsort_s v)~_j.
Proof.
move=>Pr; destruct i; destruct j; rewrite /= !(tnth_nth 0)/= =>P1.
apply: (sorted_leq_nth_in geR_transitive geR_refl _ 
  (all_geR_sort_s Pr) (sort_s_sorted Pr) m m0)=>//.
all: by rewrite inE; move: (size_sort_s v)=>/eqP->. 
Qed.

Lemma sort_v_decreasing v : v \is a realmx -> 
  forall i j : 'I_n, (i > j)%N || (sort_v v 0 i >= sort_v v 0 j).
Proof.
move=>Pr i j. rewrite !mxE. case E: (j < i)%N=>//=.
apply homo_sort_s=>//. by rewrite -(negbK (i <= j)%N) -ltnNge E.
Qed.

Lemma sort_exists v : v \is a realmx -> 
  exists (s : 'S_n), col_perm s v \is is_decreasing.
Proof.
move: (perm_sort_v v)=>[p Pp]; exists p. 
by rewrite Pp; apply/is_decreasingP; apply sort_v_decreasing.
Qed.

Lemma is_decreasing_sorted_s v : v \is is_decreasing -> sorted geR (s v).
Proof.
move=>P1; rewrite sorted_pairwise=>[x y z +P2|]; first by apply (le_trans P2).
apply/(pairwiseP 0)=>i j; rewrite !inE !size_tuple=>Pi Pj ltij.
rewrite !nth_tnth !tnth_map !tnth_ord_tuple.
move/is_decreasingP: P1=>/(_ (Ordinal Pi) (Ordinal Pj)).
by rewrite /= ltnNge leq_eqVlt ltij orbT/=.
Qed.

Lemma is_decreasing_sorted v : v \is a realmx -> 
  v \is is_decreasing -> sort_v v = v.
Proof.
move=>Pr; move/is_decreasing_sorted_s/(sorted_sort_in geR_transitive (all_geR_s Pr))=>P1.
by apply/matrixP=>i j; rewrite !ord1 !mxE (tnth_nth 0)/= /ss P1 
  nth_tnth ltn_ordK tnth_map tnth_ord_tuple.
Qed.

Lemma col_perm_perm_s v (p : 'S_n) : perm_eq (s v) (s (col_perm p v)).
Proof.
apply/tuple_permP. exists (invg p). f_equal.
by apply eq_from_tnth=>i; rewrite !tnth_map !tnth_ord_tuple mxE permKV.
Qed.

Lemma col_perm_real v (p : 'S_n) : v \is a realmx -> col_perm p v \is a realmx.
Proof. by move/realmxP=>P1; apply/realmxP=>i j; rewrite mxE P1. Qed.

Lemma is_decreasing_perm v (p : 'S_n) : v \is a realmx ->
  v \is is_decreasing -> col_perm p v \is is_decreasing -> col_perm p v = v.
Proof.
move=>P1 P2 P3; rewrite -{2}(is_decreasing_sorted P1 P2) 
  -(is_decreasing_sorted (col_perm_real p P1) P3).
apply/matrixP=>i j; rewrite !mxE !(tnth_nth 0) !tsort_sE; f_equal.
suff P x : x \in s (col_perm p v) -> x \in PR.
rewrite /ss. apply/perm_sort_inP=>[x y /P+/P|x y z _ _ _ +P5|x y _ _|].
apply geR_total. apply (le_trans P5). by rewrite -eq_le=>/eqP->.
by rewrite perm_sym col_perm_perm_s. 
move=>P4; move: P4 {+}P4=>/(nth_index 0) {2}<-; rewrite -index_mem size_tuple=>P4.
by rewrite nth_tnth tnth_map; apply/realmxP/col_perm_real.
Qed.

Lemma poly_prod_perm_seq (T: idomainType) (F G : seq T) :
  \prod_(a <- F) ('X - a%:P) = \prod_(a <- G) ('X - a%:P)
  -> perm_eq F G.
Proof.
elim: F G=>[G P1|x r IH G]; last rewrite big_cons => P1.
have: size G = 0%N by apply/PeanoNat.Nat.succ_inj; rewrite 
  -(size_prod_XsubC _ idfun)/= -P1 size_prod_XsubC. by case: G P1.
have: x \in G by rewrite -root_prod_XsubC -P1 rootM root_XsubC eqxx.
move/perm_to_rem=>P2; move: P1; rewrite (perm_big _ P2)/= big_cons.
suff P1: GRing.lreg ('X - x%:P). move/P1/IH.
by rewrite -(perm_cons x) perm_sym [in X in _ -> X]perm_sym=>/(perm_trans P2).
apply/lreg_lead; rewrite lead_coefXsubC; apply lreg1.
Qed.

Lemma poly_prod_perm m (T: idomainType) (F G : 'I_m -> T) :
  \prod_(i < m) ('X - (F i)%:P) = \prod_(i < m) ('X - (G i)%:P)
  -> exists (s : 'S_m), forall i, F (s i) = G i.
Proof.
set sf := fun (f:'I_m -> T) => [tuple of [seq f i | i <- ord_tuple m]].
have Pf f: \prod_(i < m) ('X - (f i)%:P) = \prod_(a <- (sf f)) ('X - a%:P).
by rewrite /sf/= big_map enumT /index_enum !unlock.
rewrite !Pf=>/poly_prod_perm_seq; move/tuple_permP=>[p Pp].
exists (invg p)=>i. 
rewrite -(tnth_ord_tuple (invg p i)) -tnth_map -/sf/= (tnth_nth 0) Pp.
by rewrite nth_tnth /sf !tnth_map !tnth_ord_tuple ltn_ordK permKV.
Qed.

Lemma poly_unique_sort (u v : 'rV[R]_n) :
  char_poly (diag_mx u) = char_poly (diag_mx v) -> 
    exists (p : 'S_n), col_perm p u = v.
Proof.
rewrite !char_poly_trig ?diag_mx_is_trig// =>/poly_prod_perm[p Pp].
exists p; apply/matrixP=>i j; rewrite !mxE !ord1.
by move: (Pp j); rewrite !mxE !eqxx !mulr1n.
Qed.

End sort_real_vect.

Arguments is_decreasing {R n}.

Section diag_decreasing.
Variable (R: numClosedFieldType) (n:nat).
Implicit Type (v : 'rV[R]_n).

Lemma perm_mx_unitary (s : 'S_n) : (@perm_mx R n s) \is unitarymx.
Proof.
apply/unitarymxP/matrixP=>i j; rewrite !mxE.
under eq_bigr do rewrite /perm_mx !mxE.
rewrite (bigD1 (s i))//= big1.
by move=>k /negPf nki; rewrite eq_sym nki mul0r.
by rewrite eqxx (inj_eq perm_inj) addr0 mul1r eq_sym conjC_nat.
Qed.

Lemma trC_perm_mx (s : 'S_n) : (@perm_mx R n s)^*t = perm_mx (invg s).
Proof. by apply/matrixP=>i j; rewrite !mxE conjC_nat (canF_eq (permK s)) eq_sym. Qed.

Definition is_svd_diag := 
  [qualify v : 'rV[R]_n | (v \is a nnegmx) && (v \is is_decreasing)].

Lemma svd_diag_decreasing v : v \is is_svd_diag -> v \is is_decreasing.
Proof. by move/andP=>[_ ->]. Qed.

Lemma svd_diag_nneg v : v \is is_svd_diag -> v \is a nnegmx.
Proof. by move/andP=>[->]. Qed.

Lemma svd_diag_real v : v \is is_svd_diag -> v \is a realmx.
Proof. by move/svd_diag_nneg/nnegmx_real. Qed.

Lemma svd_diag_ge0 v i : v \is is_svd_diag -> v 0 i >= 0.
Proof. by rewrite -nnegrE; move/svd_diag_nneg/nnegmxP=>/(_ 0 i). Qed.

Lemma is_svd_diagP v : reflect (forall i : 'I_n, (v 0 i >= 0) 
  /\ forall j : 'I_n, (i > j)%N || (v 0 i >= v 0 j))
    (v \is is_svd_diag).
Proof.
apply/(iffP andP)=>[[Nn De i]|IH]; 
  (split; [apply/nnegmxP=>// i j | apply/is_decreasingP=>// i j]).
by rewrite ord1 nnegrE; move: (IH j)=>[->].
by move: (IH i)=>[_ /(_ j)].
Qed.

Lemma is_svd_diag_eq0 v i : v \is is_svd_diag -> v 0 i = 0 -> 
  forall j : 'I_n, (j >= i)%N -> v 0 j = 0.
Proof.
move/is_svd_diagP=>P1 P2 j ltij; move: (P1 j) (P1 i) =>[Pj _] [_ /(_ j)].
by rewrite ltnNge ltij/= P2=>Pjn; apply/eqP; rewrite eq_le Pj Pjn.
Qed.

Lemma is_svd_diag_neq0 v i : v \is is_svd_diag -> v 0 i != 0 -> 
  forall j : 'I_n, (j <= i)%N -> v 0 j != 0.
Proof.
move/is_svd_diagP=>P1 P2 j ltij; move: (P1 i) (P1 j) =>[Pi _] [_ /(_ i)].
rewrite ltnNge ltij/= => Pij; apply/lt0r_neq0.
by apply: (lt_le_trans _ Pij); rewrite lt_def P2 Pi.
Qed.

Lemma sqrt_svd_diag p v : v \is is_svd_diag -> p.-rootdmx v \is is_svd_diag.
Proof.
move/is_svd_diagP=>P; apply/is_svd_diagP=>i/=; rewrite !mxE.
case: p=>[|p]; first by rewrite !root0C; split=>// j; rewrite mxE root0C lexx orbT. 
split=>[|j]; first by rewrite rootC_ge0//; move: (P i)=>[->].
move: (P j) (P i) =>[P3 _] [P1 /(_ j)]/orP[->//|P2].
by rewrite !mxE ler_rootC// P2 orbT.
Qed.

Lemma sqr_svd_diag p v : v \is is_svd_diag -> v.^+p \is is_svd_diag.
Proof.
move/is_svd_diagP=>P; apply/is_svd_diagP=>i/=; rewrite !mxE; case: p=>[|p].
by rewrite !expr0 ler01; split=>// j; rewrite mxE expr0 lexx orbT. 
split=>[|j]; first by apply/exprn_ge0; move: (P i)=>[->].
move: (P j) (P i) =>[P3 _] [P1 /(_ j)]/orP[->//|P2].
by rewrite !mxE ler_pXn2r// P2 orbT.
Qed.

Lemma svd_diag_conj v : v \is is_svd_diag -> v ^*m = v.
Proof. 
move/is_svd_diagP=>P; apply/matrixP=>i j.
by rewrite !mxE !ord1 geC0_conj//; move: (P j)=>[->].
Qed.

Lemma svd_diagZ v a : v \is is_svd_diag -> 0 <= a -> a *: v \is is_svd_diag.
Proof.
move/is_svd_diagP=>P1 P2; apply/is_svd_diagP=>i; split. 
by rewrite !mxE mulr_ge0//; move: (P1 i)=>[->].
move=>j; move: (P1 i)=>[_ /(_ j)]/orP[->//| P3].
by rewrite !mxE ler_wpM2l// orbT.
Qed.

Lemma const_svd_diag a : 0 <= a -> const_mx a \is is_svd_diag.
Proof.
move=>P1; apply/is_svd_diagP=>i.
split=>[|j]; by rewrite !mxE// lexx orbT.
Qed.

Lemma descreasing_row_vec v : v \is a nnegmx ->
  exists (s : 'S_n), col_perm s v \is is_svd_diag.
Proof.
move=>Nn; move: {+}Nn=>/nnegmx_real/sort_exists=>[[s Ps]].
exists s. apply/andP; split=>//; apply/nnegmxP=>i j.
by move/nnegmxP: Nn=>Nn; rewrite !mxE Nn.
Qed.

Lemma diag_perm (s : 'S_n) v :
  diag_mx (col_perm s v) = perm_mx s *m diag_mx v *m (perm_mx s)^*t.
Proof.
rewrite trC_perm_mx; apply/matrixP=>i j; rewrite !mxE.
rewrite (bigD1 (s j))//= big1=>[k /negPf P|].
by rewrite !mxE (canF_eq (permKV s)) P mulr0.
rewrite !mxE (bigD1 (s i))//= big1=>[k /negPf P|].
by rewrite !mxE eq_sym P mul0r.
by rewrite !mxE (canF_eq (permKV s)) !eqxx (inj_eq perm_inj) !addr0 mulr1 mul1r.
Qed.

Lemma min_idl (p q: nat) : ((minn p q) + (p - q) = p)%N.
Proof. by rewrite minnE subnK// leq_subr. Qed.

Lemma min_idr (p q: nat) : ((minn p q) + (q - p) = q)%N.
Proof. by rewrite minnC min_idl. Qed.

Lemma minn_id (p: nat) : minn p p = p.
Proof. by rewrite minnE subnn subn0. Qed.

Lemma usubmx_mul p q r s (A : 'M[R]_(p+q,r)) (B : 'M[R]_(r,s)) :
  usubmx (A *m B) = usubmx A *m B.
Proof. by apply/row_matrixP=>i; rewrite !row_usubmx !row_mul row_usubmx. Qed.

Lemma castmx_usubmx p q r r' (eqr : r = r') (A : 'M[R]_(p+q,r)) :
  castmx (erefl p, eqr) (usubmx A) =  usubmx (castmx (erefl _, eqr) A).
Proof. by case: r' / eqr A => A; rewrite !castmx_id. Qed.

Lemma row_mx_cast0 p q (A : 'M[R]_(p,q)) :
  A = castmx (erefl _, addn0 q) (row_mx A 0).
Proof.
apply/esym/(canLR (castmxKV _ _))=>/=.  
apply/matrixP=>i j. rewrite castmxE/= cast_ord_id esymK mxE -{2}(splitK j).
case: (fintype.split j)=>a/=; destruct a=>//=.
f_equal. by apply ord_inj=>/=.
Qed.

Lemma col_mx_cast0 p q (A : 'M[R]_(p,q)) :
  A = castmx (addn0 p, erefl _) (col_mx A 0).
Proof. by apply/trmx_inj; rewrite trmx_cast/= tr_col_mx linear0 -row_mx_cast0. Qed.

Lemma block_mx_castc0 p q r (A : 'M[R]_(p,q)) (B : 'M[R]_(p,r)) :
  (row_mx A B) = castmx (addn0 p, erefl _) (block_mx A B 0 0).
Proof. by rewrite /block_mx row_mx0 -col_mx_cast0. Qed.

Lemma block_mx_cast00 p q (A : 'M[R]_(p,q)) :
  A = castmx (addn0 p, addn0 q) (block_mx A 0 0 0).
Proof. 
by rewrite -[addn0 p]etrans_ereflV -[addn0 q]etrans_erefl 
  -castmx_comp -block_mx_castc0 -row_mx_cast0.
Qed.

Definition cdiag_mx p q (D : 'rV[R]_(minn p q)) : 'M[R]_(p,q)
  := castmx (min_idl p q, min_idr p q) (block_mx (diag_mx D) 0 0 0).

Lemma map_cdiag_mx (f : {rmorphism R -> R}) p q (d : 'rV_(minn p q)) :
  map_mx f (cdiag_mx d) = cdiag_mx (map_mx f d).
Proof. by rewrite /cdiag_mx map_castmx map_block_mx !raddf0 map_diag_mx. Qed.

Lemma cdiag_adjmx p q (D : 'rV[R]_(minn p q)) :
 (cdiag_mx D)^*t = cdiag_mx (castmx (erefl _, minnC _ _) (D^*m)).
Proof.
rewrite /cdiag_mx castmx_funE/= adjmxE tr_block_mx map_block_mx !raddf0 -adjmxE 
  diag_mx_adj; apply/(canLR (castmxKV _ _))=>/=; rewrite castmx_comp.
move: (etrans (min_idl q p) (esym (min_idr p q)))=>E1.
move: (etrans (min_idr q p) (esym (min_idl p q))) (minnC p q) =>E2 E3.
by case: (minn q p) / E3 E1 E2=> E1 E2; rewrite !castmx_id.
Qed.

Lemma cdiag_conjmx p q (D : 'rV[R]_(minn p q)) :
 (cdiag_mx D)^*m = cdiag_mx (D^*m).
Proof. by rewrite /cdiag_mx castmx_funE conjmxE map_block_mx !raddf0 map_diag_mx. Qed.

Lemma cdiag_trmx p q (D : 'rV[R]_(minn p q)) :
 (cdiag_mx D)^T = cdiag_mx (castmx (erefl _, minnC _ _) D).
Proof. by rewrite -[LHS]conjmxK -adjmxTC cdiag_adjmx cdiag_conjmx castmx_funE conjmxK. Qed.

Lemma cdiag_mx_diag p (D : 'rV[R]_(minn p p)) :
  cdiag_mx D = diag_mx (castmx (erefl _, minn_id _) D).
Proof.
rewrite /cdiag_mx. move: (min_idl p p) (esym (minn_id p))=>E1 E2.
rewrite (eq_irrelevance (min_idr p p) E1) (eq_irrelevance (minn_id p) (esym E2)) 
  diagmx_cast; case: (minn p p) / E2 E1 D=> E1 D.
move: (subnn p)=>/esym E3; case: (p - p)%N / E3 E1=>E1. 
by rewrite (eq_irrelevance E1 (addn0 p)) -block_mx_cast00/= castmx_id.
Qed.

Definition svd_d_exdl p q (D : 'rV[R]_(minn p q)) :=
  (castmx (erefl _, min_idl p q) (row_mx D 0)).

Definition svd_d_exdr p q (D : 'rV[R]_(minn p q)) :=
  (castmx (erefl _, min_idr p q) (row_mx D 0)).

Lemma svd_d_exdl_inj p q : injective (@svd_d_exdl p q).
Proof. 
by move=>D D' /castmx_sym; 
  rewrite castmxK=>/(f_equal lsubmx); rewrite !row_mxKl.
Qed.

Lemma svd_d_exdr_inj p q : injective (@svd_d_exdr p q).
Proof. 
by move=>D D' /castmx_sym;
  rewrite castmxK=>/(f_equal lsubmx); rewrite !row_mxKl.
Qed.

Lemma svd_d_exdr_conj p q (D : 'rV[R]_(minn p q)) :
  svd_d_exdr D^*m = (svd_d_exdr D)^*m.
Proof. by rewrite /svd_d_exdr castmx_funE !conjmxE map_row_mx raddf0. Qed.

Lemma big_ord_cast m m' (eqm : m' = m) (P: pred 'I_m) (F : 'I_m -> R) :
  \sum_(i | P i) F i = \sum_(i | P (cast_ord eqm i)) F (cast_ord eqm i).
Proof. case: m / eqm P F=>P F. apply eq_big=>[i|i Pi]; by rewrite cast_ord_id. Qed.

Lemma svd_d_exd_sumr p q (D: 'rV[R]_(minn p q)) (f: R-> R) :
  f 0 = 0 -> \sum_i f (D 0 i) = \sum_i f (svd_d_exdr D 0 i).
Proof.
move=>P1; rewrite /svd_d_exdl; move: (min_idr p q)=>P2.
rewrite (big_ord_cast P2) big_split_ord/= [X in _ + X]big1 ?addr0; last apply eq_bigr.
all: by move=>i _; rewrite castmxE/= ord1 cast_ord_comp 
  cast_ord_id ?row_mxEr ?row_mxEl// mxE P1.
Qed.

Lemma svd_d_exd_suml p q (D: 'rV[R]_(minn p q)) (f: R-> R) :
  f 0 = 0 -> \sum_i f (D 0 i) = \sum_i f (svd_d_exdl D 0 i).
Proof.
move=>P1; rewrite /svd_d_exdl; move: (min_idl p q)=>P2.
rewrite (big_ord_cast P2) big_split_ord/= [X in _ + X]big1 ?addr0; last apply eq_bigr.
all: by move=>i _; rewrite castmxE/= ord1 cast_ord_comp 
  cast_ord_id ?row_mxEr ?row_mxEl// mxE P1.
Qed.

Lemma cdiag_mx_mull p q (D D': 'rV[R]_(minn p q)) :
  (cdiag_mx D) *m (cdiag_mx D')^*t = diag_mx ((svd_d_exdl D) .* (svd_d_exdl D' ^*m)).
Proof.
rewrite /cdiag_mx castmx_funE/= castmx_mul adjmxE tr_block_mx map_block_mx !raddf0/=.
rewrite mulmx_block !mulmx0 !mul0mx !addr0 -adjmxE.
rewrite /svd_d_exdl diag_mx_adj diag_mx_dmul.
apply/matrixP=>i j; rewrite !mxE !castmxE/=.
set i' := (cast_ord (esym (min_idl p q)) i).
set j' := (cast_ord (esym (min_idl p q)) j).
have ->: i == j = (i' == j') by rewrite -[RHS](inj_eq (@ord_inj _))/=.
rewrite !mxE -{4}(splitK i') -{3}(splitK j').
case: (fintype.split i')=>a; rewrite ?mxE; 
  case: (fintype.split j')=>b/=; rewrite !mxE ?ord1 ?mul0r ?mul0rn//.
by rewrite eq_lrshift mulr0n.
Qed.

Lemma cdiag_mx_mulr p q (D D': 'rV[R]_(minn p q)) :
  (cdiag_mx D)^*t *m (cdiag_mx D') = diag_mx ((svd_d_exdr D ^*m) .* (svd_d_exdr D')).
Proof.
rewrite /cdiag_mx castmx_funE/= castmx_mul adjmxE tr_block_mx map_block_mx !raddf0/=.
rewrite mulmx_block !mulmx0 !mul0mx !addr0 -adjmxE.
rewrite /svd_d_exdl diag_mx_adj diag_mx_dmul.
apply/matrixP=>i j; rewrite !mxE !castmxE/=.
set i' := (cast_ord (esym (min_idr p q)) i).
set j' := (cast_ord (esym (min_idr p q)) j).
have ->: i == j = (i' == j') by rewrite -[RHS](inj_eq (@ord_inj _))/=.
rewrite !mxE -{4}(splitK i') -{3}(splitK j').
case: (fintype.split i')=>a; rewrite ?mxE; 
  case: (fintype.split j')=>b/=; rewrite !mxE ?ord1 ?mulr0 ?mul0rn//.
by rewrite eq_lrshift mulr0n.
Qed.

Lemma pnorm_cdiag m p q (D: 'rV[R]_(minn p q)) :
  pnorm m (cdiag_mx D) = pnorm m D.
Proof.
rewrite !pnorm_pair big_ord1 /cdiag_mx; f_equal.
move: (min_idl p q) (min_idr p q)=>P1 P2.
rewrite (big_ord_cast P1) big_split_ord/= [X in _ + X]big1 ?addr0; last apply eq_bigr.
all: move=>i _; rewrite (big_ord_cast P2) big_split_ord/= [X in _ + X]big1.
2: rewrite big1 ?addr0//. 4: rewrite (bigD1 i)//= big1=>[k /negPf nk|].
1,2,3: move=>k _. all: by rewrite castmxE/= !cast_ord_comp !cast_ord_id 
  ?block_mxEul ?block_mxEur ?block_mxEdl ?block_mxEdr mxE 1?eq_sym ?nk 
  ?mulr0n ?normr0 ?expr0n// eqxx mulr1n !addr0.
Qed.

Lemma l1norm_cdiag p q (D: 'rV[R]_(minn p q)) : l1norm (cdiag_mx D) = l1norm D.
Proof. exact: pnorm_cdiag. Qed.
Lemma l2norm_cdiag p q (D: 'rV[R]_(minn p q)) : l2norm (cdiag_mx D) = l2norm D.
Proof. exact: pnorm_cdiag. Qed.

Lemma cdiag_mx_is_linear p q : linear (@cdiag_mx p q).
Proof. 
by move=>a A B; rewrite /cdiag_mx linearP/= -[RHS]linearP/= 
  scale_block_mx add_block_mx !scaler0 !addr0.
Qed.
HB.instance Definition _ p q :=
  GRing.isLinear.Build R 'rV_(minn p q) 'M_(p, q) *:%R
    (@cdiag_mx p q) (@cdiag_mx_is_linear p q).

End diag_decreasing.

Arguments is_svd_diag {R n}.

(* from spectral decomposition to svd *)
Section SingularValueDecomposition.
Variable (R: numClosedFieldType).
 (* (m n: nat) Hypothesis (lenm : (m <= n)%N). *)

Local Notation "''[' u , v ]" := (dotmx u v) : ring_scope.
Local Notation "''[' u ]" := '[u, u]%R : ring_scope.

Lemma formV_psd p q (M : 'M[R]_(p,q)) : (M ^*t *m M) \is psdmx.
Proof.
by apply/psdmx_dot=>v; rewrite mulmxA -adjmxM -mulmxA 
  nnegrE dotV_l2norm exprn_ge0// pnorm_ge0.
Qed.

Lemma form_psd p q (M : 'M[R]_(p,q)) : (M *m M ^*t) \is psdmx.
Proof. by rewrite -{1}(adjmxK M) formV_psd. Qed.

Lemma psdmx_form (n : nat) (A : 'M[R]_n) :
  A \is psdmx -> exists B : 'M[R]_n , A = B *m B^*t.
Proof.
move=>/psdmxP[/hermmx_normal/eigen_dec P1 /nnegmxP P2].
exists ((eigenmx A) *m diag_mx (sqrtdmx (spectral_diag A))).
rewrite adjmxM {1}P1 !mulmxA. f_equal.
rewrite -!mulmxA. f_equal. rewrite diag_mx_adj diag_mx_dmul. f_equal.
apply/matrixP=>i j; rewrite !mxE -normCK real_normK ?sqrtCK// realE sqrtC_ge0.
apply/orP; left; by apply P2.
Qed.

Lemma psdmx_formV (n : nat) (A : 'M[R]_n) :
  A \is psdmx -> exists B : 'M[R]_n , A = B^*t *m B.
Proof. by move=>/psdmx_form[B PB]; exists (B^*t); rewrite adjmxK. Qed.

Lemma psdmx_svd p (M : 'M[R]_p) : M \is psdmx -> (exists sdpsd : 'M_p * 'rV_p, 
  [&& (sdpsd.1 \is unitarymx),  (sdpsd.2 \is is_svd_diag) &
  (M == sdpsd.1^*t *m diag_mx sdpsd.2 *m sdpsd.1)]).
Proof.
move=>/psdmxP [/hermmx_normal/eigen_dec P1 /descreasing_row_vec [s Ps]].
exists (perm_mx s *m (eigenmx M)^*t, col_perm s (spectral_diag M))=>/=.
apply/and3P; split=>//.
  apply/mul_unitarymx; [apply/perm_mx_unitary|rewrite trmxC_unitary//].
by rewrite diag_perm adjmxM !mulmxA !mulmxKtV// ?perm_mx_unitary// adjmxK; apply/eqP.
Qed.

Lemma dot_dotmxE p q (A B : 'M[R]_(p,q)) i j : 
  (A *m B ^*t) i j = '[ (row i A), (row j B)].
Proof. by rewrite dotmxE !mxE; apply eq_bigr=>k _; rewrite !mxE. Qed.

Lemma mulmx_colrow {T : ringType } p q r (A : 'M[T]_(p,q)) (B : 'M[T]_(q,r)) : 
  (A *m B) = \sum_i  (col i A) *m (row i B).
Proof. 
apply/matrixP=>i j. rewrite !mxE summxE. apply eq_bigr=> k _.
by rewrite !mxE big_ord1 !mxE.
Qed.

Lemma row_diag_mul {T : ringType} p q (D : 'rV[T]_p) (A : 'M[T]_(p,q)) i : 
  row i (diag_mx D *m A) = D 0 i *: row i A.
Proof.
apply/matrixP=>j k; rewrite !mxE (bigD1 i)//= big1.
by move=>l /negPf nli; rewrite !mxE eq_sym nli mulr0n mul0r.
by rewrite mxE eqxx mulr1n addr0.
Qed.

Lemma ord_ltn_ind k P : 
  (forall i : 'I_k, (forall j : 'I_k, (j < i)%N -> P j) -> P i) -> forall i, P i.
Proof.
move=>H i; case: i=>p; elim/ltn_ind: p=> p IH ltmk.
by apply H=>j; case: j=>/= t lttk lttm; apply IH.
Qed.

Lemma unitary_dim m n (U: 'M[R]_(m,n)) : U \is unitarymx -> (m <= n)%N.
Proof. move/mxrank_unitary=>P1; move: (rank_leq_col U); by rewrite P1. Qed.

Lemma unitary_ext m n (U: 'M[R]_(m,n)) : U \is unitarymx -> 
  U = usubmx (schmidt (col_mx U (0 : 'M[R]_(n-m,_)))).
Proof.
move=>UU; move: {+}UU=>/row_unitarymxP Ur; apply/row_matrixP=>i.
set V := (col_mx U 0).
have P1 j : row j U = row (lshift _ j) V by rewrite /V rowKu.
rewrite P1 row_usubmx; elim/ord_ltn_ind: i=> i Hi.
move: (row_schmidt_sub V (lshift (n - m) i))=>/sub_sums_genmxP[u_].
have P2: (m + (n - m) <= n)%N by rewrite (subnKC (unitary_dim UU)).
move: (schmidt_unitarymx V P2)=>/row_unitarymxP PA.
have P7 i0 : u_ i0 *m row i0 (schmidt V) = u_ i0 0 0 *: row i0 (schmidt V).
  by apply/matrixP=>r q; rewrite 1 ?mxE big_ord1 !ord1 !mxE.
under eq_bigr do rewrite P7.
rewrite big_split_ord/= [X in _ + X]big1=>[j|P3].
by destruct i=>/= P3; move: (leq_trans (leq_addr _ _) P3); rewrite leqNgt i.
move: {+}P3; rewrite (bigD1 i)//= big1=>[j|P5].
rewrite andbC -ltn_neqAle=>P4; move: (Ur i j).
rewrite !P1 P3 addr0 linear_suml/= (bigD1 j)/=; first by apply ltnW.
rewrite big1=>[k /andP[_ /negPf nkj]|].
1,2: rewrite linearZl_LR/= (Hi _ P4) PA eq_lshift ?nkj ?mulr0// eqxx mulr1 addr0 
-(inj_eq (@ord_inj _)) (gtn_eqF P4)=>->. by rewrite scale0r.
move: (form1_row_schmidt V (lshift (n - m) i)) (Ur i i).
rewrite P1 P5 !addr0 !linearZl_LR linearZr_LR /= mulrA -normCK !PA !eqxx 
  !mulr1=>P4 /(f_equal sqrtC); rewrite sqrCK// sqrtC1 -{2}(ger0_norm P4)=>->.
by rewrite scale1r.
Qed.

Lemma form_diag_schmidt p (A : 'M[R]_p) (D : 'rV[R]_p): 
  D \is is_svd_diag -> A *m A ^*t = diag_mx D ->
  A = diag_mx (sqrtdmx D) *m schmidt A.
Proof.
move=>P1 P2; have P3 i j : '[ (row i A), (row j A)] = D 0 i *+ (i == j) 
  by rewrite -dot_dotmxE P2 !mxE.
apply/row_matrixP=>i; rewrite row_diag_mul mxE.
move: (schmidt_unitarymx A (leqnn _))=>/row_unitarymxP PA.
elim/ord_ltn_ind: i=> i Hi; move: (P3 i i); rewrite eqxx mulr1n.
case E: (D 0 i == 0); move/eqP: E.
  by move=>->; rewrite sqrtC0 scale0r=>/eqP; rewrite dnorm_eq0=>/eqP.
move/eqP=>P4 Q1; move: (is_svd_diag_neq0 P1 P4)=>P5.
move: (row_schmidt_sub A i)=>/sub_sums_genmxP[u_].
have P7 i0 : u_ i0 *m row i0 (schmidt A) = u_ i0 0 0 *: row i0 (schmidt A)
  by apply/matrixP=>r q; rewrite 1 ?mxE big_ord1 !ord1 !mxE.
under eq_bigr do rewrite P7; move=>P6.
have P8: forall j : 'I_p, (j < i)%N -> u_ j 0 0 = 0.
  move=>j ltji; move: (P3 i j).
  rewrite P6 Hi// linear_suml/= (bigD1 j)/=; first by apply ltnW.
  rewrite big1; first move=>k /andP[_ /negPf nkj].
  1,2: rewrite linearZl_LR linearZr_LR /= PA ?nkj ?mulr0// ?PA eqxx mulr1 addr0. 
  case: eqP=>[E|/eqP E /eqP]; first by move: ltji; rewrite E ltnn.
  by rewrite mulr0n mulf_eq0 conjC_eq0 sqrtC_eq0 -[D 0 j == 0]negbK P5// 
    1 ?leq_eqVlt ?ltji ?orbT// ?orbF =>/eqP.
have P9: row i A = u_ i 0 0 *: row i (schmidt A).
  rewrite P6 (bigD1 i)//= big1=>[j|]; 
  by rewrite ?addr0// andbC -ltn_neqAle=>/P8->; rewrite scale0r.
have Q2 : `|u_ i 0 0| = sqrtC (D 0 i). move: (P3 i i).
  rewrite P9 linearZl_LR linearZr_LR /= PA !eqxx mulr1 -normCK mulr1n.
  by move/(f_equal sqrtC); rewrite sqrCK.
have Q3 : u_ i 0 0 >= 0.
  by move: (form1_row_schmidt A i); rewrite P9 linearZl_LR/= PA eqxx mulr1.
by rewrite P9 -(ger0_norm Q3) Q2.
Qed.

Lemma svd_diag_exd p (D: 'rV[R]_p) q : 
  D \is is_svd_diag -> row_mx D (0 : 'rV[R]_q) \is is_svd_diag.
Proof.
move=>P1; apply/is_svd_diagP=>i; split=>[|j]; first rewrite !mxE. 
by case: (fintype.split i)=>a; [apply/nnegmxP/svd_diag_nneg | rewrite mxE].
rewrite !mxE -{1}(splitK i) -{1}(splitK j); case: (fintype.split i)=>a; 
  case: (fintype.split j)=>b/=;[|apply/orP ..]; rewrite ?mxE;
[apply/is_decreasingP/svd_diag_decreasing | right | left | right] =>//.
by apply/nnegmxP/svd_diag_nneg. by case: b=>b ltbm/=; apply ltn_addr.
Qed.

Lemma svd_diag_exdl p q (D: 'rV[R]_(minn p q)) : 
  D \is is_svd_diag -> svd_d_exdl D \is is_svd_diag.
Proof. rewrite castmx_funE; exact: svd_diag_exd. Qed.

Lemma svd_diag_exdr p q (D: 'rV[R]_(minn p q)) : 
  D \is is_svd_diag -> svd_d_exdr D \is is_svd_diag.
Proof. by rewrite castmx_funE; exact: svd_diag_exd. Qed.

Lemma form_diag_schmidt1 m n (lemn : (m <= n)%N) (A : 'M[R]_(m,n)) (D : 'rV[R]_m): 
  D \is is_svd_diag -> A *m A ^*t = diag_mx D ->
  A = castmx (erefl m, (subnKC lemn)) (row_mx (diag_mx (sqrtdmx D)) 0) 
      *m schmidt (castmx ((subnKC lemn),erefl n) (col_mx A 0)).
Proof.
move=> Dd PA; set De := castmx (erefl _, (subnKC lemn)) (row_mx D 0).
set Ae := castmx ((subnKC lemn), erefl _) (col_mx A 0).
have PDe : De \is is_svd_diag by rewrite /De castmx_funE svd_diag_exd.
have PAe: Ae *m Ae ^*t = diag_mx De by rewrite /Ae castmx_funE/= castmx_mul/= 
  /De diagmx_cast; f_equal; rewrite adjmxE tr_col_mx map_row_mx !raddf0/= 
  mul_col_row diag_mx_row PA mulmx0 !mul0mx linear0.
move: (form_diag_schmidt PDe PAe). 
move/(f_equal (castmx (esym (subnKC lemn), erefl _)))/(f_equal usubmx).
rewrite /Ae {1}esym_erefl castmxK col_mxKu=>{1}->.
rewrite -(castmx_mul (erefl n)) castmx_id usubmx_mul; congr (_ *m _).
apply/esym/(canLR (castmxKV _ _))=>/=.
rewrite /De /sqrtdmx /sqrtdmx map_castmx diagmx_cast map_row_mx diag_mx_row.
rewrite castmx_usubmx !castmx_comp /= etrans_erefl etrans_esym castmx_id.
by rewrite col_mxKu.
Qed.

Lemma svd_subproof_lemn m n (lemn : (m <= n)%N) (A : 'M[R]_(m,n)) : 
  (exists svdp : 'M_m * 'rV_m * 'M_n,
    [&& (svdp.1.1 \is unitarymx),  (svdp.1.2 \is is_svd_diag), 
        (svdp.2 \is unitarymx) &  (A == svdp.1.1 *m castmx (erefl m, (subnKC lemn)) 
                              (row_mx (diag_mx (svdp.1.2)) 0) *m svdp.2 ^*t)]).
Proof.
move: (psdmx_svd (form_psd A))=>[sdpsd]; set U0 := sdpsd.1; set D0 := sdpsd.2.
move=>/and3P [U0U D0SD /eqP P1].
have: (U0 *m A) *m (U0 *m A)^*t = diag_mx D0 
  by rewrite adjmxM mulmxA mulmxUC// -mulmxA mulUmx// mulmxA.
move/(form_diag_schmidt1 lemn D0SD); rewrite mulUmx// mulmxA=>P2.
exists ((U0^*t,(sqrtdmx D0)), 
  (schmidt (castmx ((subnKC lemn), erefl n) (col_mx (U0 *m A) 0)))^*t).
apply/and4P=>/=; rewrite !trmxC_unitary U0U schmidt_unitarymx//; split=>//.
by apply sqrt_svd_diag. by apply/eqP; rewrite adjmxK.
Qed.

Theorem svd_subproof m n (A : 'M[R]_(m,n)) : 
  (exists svdp : 'M_m * 'rV_(minn m n) * 'M_n,
    [&& (svdp.1.1 \is unitarymx),  (svdp.1.2 \is is_svd_diag), 
        (svdp.2 \is unitarymx) & 
        (A == svdp.1.1 *m cdiag_mx svdp.1.2 *m svdp.2 ^*t)]).
Proof.
wlog lemn: m n A / (m <= n)%N => [th_sym|].
case: (orP (leq_total m n))=>/th_sym; first by move=>/(_ A).
move=>/(_ (A^*t))[[[U D] V] /and4P/= [P1 P2 P3 /eqP P4]].
exists ((V, castmx (erefl _, minnC _ _ ) D), U)=>/=.
apply/and4P; split=>//; first by rewrite castmx_funE.
by rewrite -(adjmxK A) P4 !adjmxM adjmxK cdiag_adjmx svd_diag_conj// mulmxA.
move: (svd_subproof_lemn lemn A)=>[[[U D] V] /=/and4P[P1 P2 P3 /eqP P4]].
have E1: (m = minn m n) by apply/esym/minn_idPl.
set D' := castmx (erefl _, E1) D.
exists ((U,D'),V); apply/and4P; split=>//=; first by rewrite castmx_funE.
apply/eqP; rewrite P4; do 2 f_equal; rewrite /cdiag_mx block_mx_castc0; 
  do 2 apply/(canLR (castmxKV _ _))=>/=; rewrite !castmx_comp/= etrans_erefl /D'.
have E4: (m - n = 0)%N by move: {+}lemn=>/eqP.
move: (etrans (min_idl m n) (esym (addn0 m)))=>E2.
move: (etrans (min_idr m n) (esym (subnKC lemn)))=>E3.
case: (minn m n) / E1 E2 E3 D'=>E2 E3 _; rewrite castmx_id.
by case: 0%N / E4 E2=>E2; rewrite castmx_id.
Qed.

Definition svd_u m n (A : 'M[R]_(m,n)) :=
  (xchoose (svd_subproof A)).1.1.

Definition svd_d m n (A : 'M[R]_(m,n)) :=
  (xchoose (svd_subproof A)).1.2.

Definition svd_v m n (A : 'M[R]_(m,n)) :=
  (xchoose (svd_subproof A)).2.

(* for the square matrix; svds for this *)
Definition svds_d n (A : 'M[R]_n) :=
  castmx (erefl _, (minn_id _)) (svd_d A).

Lemma svds_d_svd_dl n (A : 'M[R]_n) : svds_d A = (svd_d_exdl (svd_d A)).
Proof.
rewrite /svds_d /svd_d_exdl; apply/(canLR (castmxKV _ _))=>/=.
rewrite castmx_comp/=; move: (etrans (min_idl n n) (esym (minn_id n)))=>E1.
move: (subnn n)=>/esym E2; case: (n-n)%N / E2 E1=>E1.
by rewrite (eq_irrelevance E1 (addn0 _)) -row_mx_cast0.
Qed.

Lemma svds_d_svd_dr n (A : 'M[R]_n) : svds_d A = (svd_d_exdr (svd_d A)).
Proof. by rewrite svds_d_svd_dl /svd_d_exdl 
(eq_irrelevance (min_idl _ _) (min_idr _ _)). Qed.

Lemma svd_u_unitarymx m n (A : 'M[R]_(m,n)) : svd_u A \is unitarymx.
Proof. by move: (xchooseP (svd_subproof A))=>/andP[P1]. Qed.

Lemma svd_v_unitarymx m n (A : 'M[R]_(m,n)) : svd_v A \is unitarymx.
Proof. by move: (xchooseP (svd_subproof A))=>/and4P[_ _ P1]. Qed.

Lemma svd_d_svd_diag m n (A : 'M[R]_(m,n)) : svd_d A \is is_svd_diag.
Proof. by move: (xchooseP (svd_subproof A))=>/and4P[_ P1]. Qed.

Lemma svds_d_svd_diag n (A : 'M[R]_n) : svds_d A \is is_svd_diag.
Proof. by rewrite /svds_d castmx_funE svd_d_svd_diag. Qed.

Definition svd_pE := (svd_u_unitarymx, svd_v_unitarymx, 
                      svd_d_svd_diag, svds_d_svd_diag).

Lemma svdE m n (A : 'M[R]_(m,n)) : 
  A = (svd_u A) *m cdiag_mx (svd_d A) *m (svd_v A) ^*t.
Proof. by move: (xchooseP (svd_subproof A))=>/and4P[_ _ _ /eqP P1]. Qed.

Lemma svdsE n (A : 'M[R]_n) : 
  A = (svd_u A) *m diag_mx (svds_d A) *m (svd_v A) ^*t.
Proof. by rewrite {1}[LHS]svdE /svds_d cdiag_mx_diag. Qed.

Lemma polymx_dec n (U : 'M[R]_n) : U \is unitarymx -> 
  'X%:M = (map_mx (@polyC R) (U^*t)) *m 'X%:M *m (map_mx (@polyC R) U).
Proof.
move=>/unitarymxPV P; rewrite -mulmxA mulmx_colrow; under eq_bigr do 
  rewrite -diag_const_mx row_diag_mul -scalemxAr -map_col -map_row -map_mxM mxE.
rewrite -scaler_sumr -map_mx_sum -mulmx_colrow P.
apply/matrixP=>i j; rewrite !mxE. 
by case: eqP=>/=; rewrite ?mulr1n ?mulr1// mulr0n mulr0.
Qed.

Lemma char_poly_dec n (U : 'M[R]_n) (A : 'M[R]_n) : U \is unitarymx -> 
  char_poly (U ^*t *m A *m U) = char_poly A.
Proof.
move=>PU; rewrite /char_poly /char_poly_mx {1}(polymx_dec PU) !map_mxM/= -mulmxBl 
  -mulmxBr !det_mulmx mulrC !det_map_mx mulrA -rmorphM -det_map_mx -det_mulmx.
by move/unitarymxP: PU=>->; rewrite det1 mul1r.
Qed.

Lemma spectral_unique n (U A : 'M[R]_n) (d : 'rV[R]_n) : 
  U \is unitarymx -> U ^*t *m diag_mx d *m U = A ->
      exists (s : 'S_n), col_perm s d = spectral_diag A.
Proof.
move=>UU DA; have /eigen_dec P: A \is normalmx. apply/normalmxP. 
rewrite -DA -adjmxE !adjmxM !mulmxA adjmxK mulmxtVK// [in RHS]mulmxtVK//.
by f_equal; rewrite -!mulmxA; f_equal; rewrite diag_mx_adj diag_mxC.
move: DA; rewrite {1}P=>/(f_equal char_poly).
by rewrite adjmxK !char_poly_dec// =>/poly_unique_sort.
Qed.

Lemma svd_d_spectral_perm m n (A : 'M[R]_(m,n)) : exists (s : 'S_m), 
  col_perm s ((svd_d_exdl (svd_d A)).^+2) = spectral_diag (A *m A^*t).
Proof.
apply (@spectral_unique _ ((svd_u A)^*t)). by rewrite trmxC_unitary svd_pE. 
rewrite [in RHS](svdE A) !adjmxM !adjmxK !mulmxA mulmxKtV// ?svd_pE//; f_equal; 
rewrite -mulmxA; f_equal; by rewrite cdiag_mx_mull svd_diag_conj ?dexpmx2// svd_pE.
Qed.

Lemma svds_d_spectral_perm n (A : 'M[R]_n) : exists (s : 'S_n), 
  col_perm s (svds_d A .^+2) = spectral_diag (A *m A^*t).
Proof. by rewrite svds_d_svd_dl; exact: svd_d_spectral_perm. Qed.

Lemma svd_d_unique m n (U: 'M[R]_m) (V: 'M[R]_n) (A: 'M[R]_(m,n)) 
  (v : 'rV[R]_(minn m n)) :
  U \is unitarymx -> V \is unitarymx -> v \is is_svd_diag -> 
    A = U *m cdiag_mx v *m V ^*t -> v = svd_d A.
Proof.
move=>UU UV Dv DA; move: (svd_d_spectral_perm A) (svd_diag_exdl Dv) 
  (svd_diag_exdl (svd_d_svd_diag A))=>[s2 Ps2 Dve Dde].
suff: U^*t^*t *m diag_mx (svd_d_exdl v .^+ 2) *m U^*t = A *m A^*t.
move/spectral_unique; rewrite trmxC_unitary=>/(_ UU)[s1].
rewrite -Ps2=>/(f_equal (col_perm (invg s2))).
rewrite -!col_permM fingroup.mulVg col_perm1=>P1.
have: col_perm (mulg (invg s2) s1) (svd_d_exdl v .^+ 2) 
  = (svd_d_exdl v .^+ 2) by apply/is_decreasing_perm; rewrite ?P1; 
  [apply/svd_diag_real | apply/svd_diag_decreasing ..]; apply/sqr_svd_diag.
by rewrite P1=>/(dexprm_inj (ltn0Sn 1) (svd_diag_nneg Dde) 
  (svd_diag_nneg Dve))/svd_d_exdl_inj->.
rewrite DA !adjmxM !mulmxA !adjmxK mulmxKtV//.
f_equal; rewrite -mulmxA; f_equal.
by rewrite cdiag_mx_mull svd_diag_conj// dexpmx2.
Qed.

Lemma svds_d_unique n (U V A : 'M[R]_n) (v : 'rV[R]_n) :
  U \is unitarymx -> V \is unitarymx -> v \is is_svd_diag -> 
    A = U *m diag_mx v *m V ^*t -> v = svds_d A.
Proof.
set v' := (castmx (erefl _, esym (minn_id _)) v).
move: (cdiag_mx_diag v'); rewrite {2}/v' castmxKV=><- PU PV Dv PA.
have Dv': v' \is is_svd_diag by rewrite /v' castmx_funE.
move: (svd_d_unique PU PV Dv' PA). 
rewrite /v'=>/esym/(canLR (castmxK _ _))/=; by rewrite esymK=><-.
Qed.

Lemma divr_norm_id (a : R) : a / `|a| * `|a| = a.
Proof.
case E: (a == 0); first by move/eqP: E=>->; rewrite !mul0r.
by rewrite mulrVK// unitfE normr_eq0 E.
Qed.

Lemma norm_if_id (a : R) : (if a == 0 then 1 else a / `|a|) * `|a| = a.
Proof. by case: eqP=>[->|_]; rewrite ?normr0 ?mulr0// divr_norm_id. Qed.

Lemma norm_if_norm (a : R) : `|(if a == 0 then 1 else a / `|a|)| = 1.
Proof. by case: eqP=>[_|/eqP P1]; 
rewrite ?normr1// normf_div normr_id mulfV// normr_eq0. Qed.

Lemma svds_d_const n a : svds_d (a%:M : 'M[R]_n) = const_mx `|a|.
move: (svdsE (a%:M : 'M[R]_n))=>P1.
have P2: (a%:M : 'M[R]_n) = ((if a == 0 then 1 else a/`|a|) *: 1%:M) 
  *m diag_mx (const_mx `|a|) *m (1%:M)^*t.
rewrite adjmx_const conjC1 mulmx1 -scalemxAl mul1mx.
by rewrite -linearZ/= -[LHS]diag_const_mx scalemx_const norm_if_id.
by rewrite (svds_d_unique _ _ _ P2)// ?unitarymxZ ?unitarymx1// 
  ?const_svd_diag// norm_if_norm.
Qed.

Lemma svd_d_const n a : svd_d (a%:M : 'M[R]_n) = const_mx `|a|.
Proof.
move: (@svds_d_const n a). rewrite /svds_d=>/esym/castmx_sym->.
by rewrite castmx_const.
Qed.

Lemma svd_d0 m n : svd_d (0 : 'M[R]_(m,n)) = 0.
Proof. 
have P: 0 = 1%:M *m cdiag_mx (0 : 'rV[R]_(minn m n)) *m (1%:M)^*t 
  by rewrite linear0 /= mulmx0 mul0mx.
by move: (svd_d_unique (unitarymx1 _ _) (unitarymx1 _ _) 
  (const_svd_diag _ (lexx 0)) P)=><-.
Qed.

Lemma svds_d0 n : svds_d (0 : 'M[R]_n) = 0.
Proof. by rewrite -scalemx0 svds_d_const normr0 const_mx0. Qed.

Lemma svds_d1 n : svds_d (1%:M : 'M[R]_n) = const_mx 1.
Proof. by rewrite svds_d_const normr1. Qed.

Lemma svd_d1 n : svd_d (1%:M : 'M[R]_n) = const_mx 1.
Proof. by rewrite svd_d_const normr1. Qed.

Lemma svd_dZ m n a (A : 'M[R]_(m,n)) : svd_d (a *: A) = `|a| *: svd_d A.
Proof. 
have P1: a *: A = ((if a == 0 then 1 else a/`|a|) *: svd_u A) *m 
  cdiag_mx (`|a| *: svd_d A) *m (svd_v A)^*t.
by rewrite linearZ/= -scalemxAr -!scalemxAl scalerA mulrC norm_if_id -svdE.
by rewrite (svd_d_unique _ _ _ P1)// ?svd_diagZ// ?unitarymxZ// ?norm_if_norm// svd_pE.
Qed.

Lemma svds_dZ n a (A : 'M[R]_n) : svds_d (a *: A) = `|a| *: svds_d A.
Proof. by rewrite /svds_d svd_dZ linearZ. Qed.

Lemma svd_d_adjmx m n (A:'M[R]_(m,n)) : 
  svd_d (A^*t) = castmx (erefl _, minnC _ _) (svd_d A).
Proof.
suff P1: A^*t = (svd_v A) *m cdiag_mx (castmx (erefl _, minnC _ _) (svd_d A)) 
  *m (svd_u A)^*t by rewrite -(svd_d_unique _ _ _ P1)// ?castmx_funE svd_pE.
by rewrite {1}(svdE A) !adjmxM adjmxK cdiag_adjmx svd_diag_conj// ?svd_pE// mulmxA.
Qed.

Lemma svds_d_adjmx n (A: 'M[R]_n) : svds_d (A^*t) = svds_d A.
Proof. by rewrite /svds_d svd_d_adjmx 
(eq_irrelevance (minnC n n) (erefl (minn n n))) castmx_id. Qed.

Lemma svd_d_trmx m n (A:'M[R]_(m,n)) : 
  svd_d (A^T) = castmx (erefl _, minnC _ _) (svd_d A).
Proof.
suff P1: A^T = (svd_v A)^*t^T *m cdiag_mx (castmx (erefl _, minnC _ _) (svd_d A)) 
  *m (svd_u A)^T^*t^*t by rewrite (svd_d_unique _ _ _ P1)// ?trmxC_unitary 
    ?trmx_unitary// ?trmxC_unitary// ?castmx_funE svd_pE.
by rewrite {1}(svdE A) !trmx_mul !adjmxK cdiag_trmx mulmxA.
Qed.

Lemma svds_d_trmx n (A: 'M[R]_n) : svds_d (A^T) = svds_d A.
Proof. by rewrite /svds_d svd_d_trmx 
(eq_irrelevance (minnC n n) (erefl (minn n n))) castmx_id. Qed.


Lemma svd_d_conjmx m n (A:'M[R]_(m,n)) : 
  svd_d (A^*m) = (svd_d A).
Proof. 
by rewrite -[in LHS](trmxK A) -adjmxTC svd_d_adjmx svd_d_trmx castmx_comp castmx_id.
Qed.

Lemma svds_d_conjmx n (A: 'M[R]_n) : svds_d (A^*m) = svds_d A.
Proof. by rewrite /svds_d svd_d_conjmx. Qed. 

Lemma svd_d_Ul m n U (A:'M[R]_(m,n)) : U \is unitarymx -> svd_d (U *m A) = svd_d A.
Proof.
move=>UU; suff P1: U *m A = (U *m svd_u A) *m cdiag_mx (svd_d A) *m (svd_v A)^*t
by rewrite (svd_d_unique _ _ _ P1)// ?unitarymx_mulmx_closed// svd_pE.
by rewrite {1}(svdE A) !mulmxA.
Qed.

Lemma svds_d_Ul n U (A:'M[R]_n) : U \is unitarymx -> svds_d (U *m A) = svds_d A.
Proof. by move=>UU; rewrite /svds_d svd_d_Ul. Qed.

Lemma svd_d_Ur m n U (A:'M[R]_(m,n)) : U \is unitarymx -> svd_d (A *m U) = svd_d A.
Proof.
move=>UU; suff P1: A *m U = (svd_u A) *m cdiag_mx (svd_d A) *m (U^*t *m svd_v A)^*t.
by rewrite (svd_d_unique _ _ _ P1)// ?unitarymx_mulmx_closed// ?trmxC_unitary// svd_pE.
by rewrite {1}(svdE A) adjmxM !mulmxA adjmxK.
Qed.

Lemma svds_d_Ur n U (A:'M[R]_n) : U \is unitarymx -> svds_d (A *m U) = svds_d A.
Proof. by move=>UU; rewrite /svds_d svd_d_Ur. Qed.

Lemma svd_d_unitary m n (U: 'M[R]_(m,n)) : U \is unitarymx -> svd_d U = const_mx 1.
Proof.
move=>UU; have P1: (m <= n)%N by move: (mxrank_unitary UU)=><-; apply rank_leq_col.
suff P2: U = 1%:M *m cdiag_mx (const_mx 1) *m 
  (schmidt (castmx (subnKC P1, erefl n) (col_mx U 0)))^*t^*t.
rewrite (svd_d_unique _ _ _ P2)// ?unitarymx1// ?const_svd_diag// ?ler01//.
rewrite trmxC_unitary; by apply schmidt_unitarymx.
rewrite adjmxK mul1mx; move: {+}UU=>/unitarymxP; rewrite -diag_const_mx=>P2.
rewrite {1}(@form_diag_schmidt1 _ _ P1 U _ _ P2) ?const_svd_diag//?ler01//;
f_equal; rewrite /cdiag_mx block_mx_castc0 castmx_comp/= etrans_id.
move: (min_idl m n) (min_idr m n) (subnKC P1)=>P3 P4 P5.
move: {+}P1 {+}P1=>/minn_idPl/esym P6; rewrite -subn_eq0=>/eqP/esym P7.
case: (minn m n) / P6 P3 P4; case: (m - n)%N / P7 P5=>P3 P4 P5.
rewrite (eq_irrelevance (addn0 _) P4) (eq_irrelevance P3 P5).
do ? f_equal; apply/matrixP=>i j; by rewrite !mxE sqrtC1.
Qed.

Lemma svd_d_unitaryC m n (U: 'M[R]_(m,n)) : U^*t \is unitarymx -> svd_d U = const_mx 1.
Proof. by rewrite -{2}(adjmxK U) svd_d_adjmx=>/svd_d_unitary->; rewrite castmx_const. Qed.

Lemma svd_d_unitaryT m n (U: 'M[R]_(m,n)) : U^T \is unitarymx -> svd_d U = const_mx 1.
Proof. by rewrite -{2}(trmxK U) svd_d_trmx=>/svd_d_unitary->; rewrite castmx_const. Qed.

Lemma svds_d_unitary m (U: 'M[R]_m) : U \is unitarymx -> svds_d U = const_mx 1.
Proof. by rewrite /svds_d=>/svd_d_unitary->; rewrite castmx_const. Qed.

Lemma svd_d_ge0 m n (A: 'M[R]_(m,n)) i : svd_d A 0 i >= 0.
Proof. by apply/svd_diag_ge0/svd_d_svd_diag. Qed.

Lemma svds_d_ge0 m (A: 'M[R]_m) i : svds_d A 0 i >= 0.
Proof. by rewrite /svds_d castmxE/= ord1 svd_d_ge0. Qed.

Lemma svd_cdiagmx m n (D: 'rV[R]_(minn m n)) : D \is is_svd_diag -> 
  svd_d (cdiag_mx D) = D.
Proof.
move=>D1; suff P1: (cdiag_mx D) = 1%:M *m (cdiag_mx D) *m (1%:M)^*t.
  by rewrite -(svd_d_unique _ _ _ P1)// ?unitarymx1//. 
by rewrite mul1mx adjmx_const conjC1 mulmx1.
Qed.

Lemma svd_diagmx n (D : 'rV[R]_n) : D \is is_svd_diag -> 
  svd_d (diag_mx D) = castmx (erefl _, esym (minn_id _)) D.
Proof.
move=>D1; suff P1: (diag_mx D)= 1%:M *m(cdiag_mx(castmx(erefl _,esym(minn_id n)) D)) 
  *m (1%:M)^*t by rewrite (svd_d_unique _ _ _ P1)// ?unitarymx1// castmx_funE. 
by rewrite mul1mx adjmx_const conjC1 mulmx1 cdiag_mx_diag castmx_comp/= castmx_id.
Qed.

Lemma svds_diagmx n (D : 'rV[R]_n) : D \is is_svd_diag -> svds_d (diag_mx D) = D.
Proof. by rewrite /svds_d=>/svd_diagmx->; rewrite castmx_comp castmx_id. Qed.

End SingularValueDecomposition.

(* remove after updating to mathcomp 2.2.0 *)
Lemma bigmax_le_elem (d : unit) (T : porderType d) I (r : seq I) (P : pred I)
  (F : I -> T) i0 x: 
  P i0 -> (x <= F i0)%O -> 
    (forall i, P i -> F i <= F i0)%O ->
      (\big[Order.max/x]_(i <- r| P i) F i <= F i0)%O.
Proof.
move=>Pi0 lei0 H; elim/big_rec:_=>[//|j y Pj Py].
by rewrite /Order.max; case: (F j < y)%O=>[//|]; apply H.
Qed.

Lemma bigmax_eq_elem (d : unit) (T : porderType d) (I : eqType) 
  (r : seq I) i0 (P : pred I) 
  (F : I -> T) x: P i0 -> (x <= F i0)%O -> i0 \in r ->
  (forall i, P i -> F i <= F i0)%O ->
  (\big[Order.max/x]_(i <- r| P i) F i)%O = F i0.
Proof.
move=>Pi0 lei0 +H; elim: r=>[//|j r IH]; rewrite inE=>/orP[/eqP<-|].
by rewrite big_cons Pi0 max_l//; apply bigmax_le_elem.
by rewrite big_cons; case E: (P j)=>///IH IH1; rewrite max_r// IH1; apply H.
Qed.

Lemma bigmax_find (d : unit) (T : porderType d) (I : finType) i0 (P : pred I) 
  (F : I -> T) x: P i0 -> (x <= F i0)%O -> (forall i, P i -> F i <= F i0)%O ->
  (\big[Order.max/x]_(i | P i) F i)%O = F i0.
Proof. by move=>Pi0 lei0 IH; apply: (bigmax_eq_elem Pi0 lei0 _ IH). Qed.
Arguments bigmax_find {d T I} i0 {P F x}.

Section Induced2Norm.
Variable (R: numClosedFieldType).

Definition c0 m n := (cast_ord (esym (minnSS _ _)) (0 : 'I_((minn m n).+1))).
Arguments c0 {m n}.

Lemma svd_d_exdr0 m n (D : 'rV[R]_(minn m.+1 n.+1)) :
  svd_d_exdr D 0 0 = D 0 c0.
Proof. 
rewrite /svd_d_exdr castmxE ord1 mxE/= /c0; move: (esym (minnSS m n))=>P1.
move: (esym (min_idr m.+1 n.+1))=>P2; case: (minn m.+1 n.+1) / P1 D P2=>D P2.
have ->: (cast_ord P2 0) = @lshift _ _ 0 by apply/ord_inj.
by case: split_ordP=>// j /lshift_inj<-; f_equal; apply/ord_inj.
Qed.

Lemma max_svd_diag_Sn m n (D : 'rV[R]_(minn m.+1 n.+1)) : D \is is_svd_diag -> 
  \big[maxr/0%:R]_i (D 0 i) = D 0 c0.
Proof.
move=>PD. apply/bigmax_find=>//[|i _].
by apply/nnegmxP/svd_diag_nneg.
by move/svd_diag_decreasing/is_decreasingP: PD=>/(_ c0 i).
Qed.

Definition i2norm m n (M : 'M[R]_(m,n)) := \big[maxr/0%:R]_i (svd_d M 0 i).

Lemma i2norms m (M : 'M[R]_m) : 
  i2norm M = \big[maxr/0%:R]_i (svds_d M 0 i).
Proof.
rewrite /i2norm /svds_d.
move: (minn_id m) (minn_id m)=>/esym P1 P2.
rewrite (eq_irrelevance P2 (esym P1)). clear P2.
set t := svd_d M. destruct t.
case: (minn m m) / P1 f=>f. by rewrite castmx_id.
Qed.

Lemma i2norm_adjmx m n (M : 'M[R]_(m,n)) : i2norm (M^*t) = i2norm M.
Proof. rewrite /i2norm svd_d_adjmx. move: (minnC m n)=>P1.
case: (minn n m) / P1. by under eq_bigr do rewrite castmx_id. Qed.

Lemma i2norm_trmx m n (M : 'M[R]_(m,n)) : i2norm (M^T) = i2norm M.
Proof. rewrite /i2norm svd_d_trmx. move: (minnC m n)=>P1.
case: (minn n m) / P1. by under eq_bigr do rewrite castmx_id. Qed.

Lemma i2norm_conjmx m n (M : 'M[R]_(m,n)) : i2norm (M^*m) = i2norm M.
Proof. by rewrite /i2norm svd_d_conjmx. Qed.

Lemma i2norm_n0 m (M : 'M[R]_(m,0)) : i2norm M = 0%:R.
Proof. by rewrite /i2norm big_ord0. Qed.

Lemma i2norm_0n m (M : 'M[R]_(0,m)) : i2norm M = 0%:R.
Proof.
rewrite /i2norm. have P1: 0%N = minn 0 m by rewrite minnC.
set t := svd_d M. case: t; case: (minn 0 m) / P1=>t; by rewrite big_ord0.
Qed.  

Lemma i2norm_Sn m n (M : 'M[R]_(m.+1,n.+1)) : i2norm M = svd_d M 0 c0.
Proof. by rewrite /i2norm max_svd_diag_Sn// svd_pE. Qed.

Lemma i2norms_Sn m (M : 'M[R]_m.+1) : i2norm M = svds_d M 0 0.
Proof. by rewrite i2norm_Sn /svds_d castmxE ord1; f_equal; apply/ord_inj=>/=. Qed.

Lemma i2norm0_eq0 m n (A : 'M[R]_(m,n)) : i2norm A = 0 -> A = 0.
Proof.
case: m A=>[A _|m]; last case: n=>[A _|n A]. 1,2: by rewrite mx_dim0E.
rewrite i2norm_Sn {2}(svdE A) mulmxUC ?mulUmx ?svd_pE// mul0mx mulmx0.
move/is_svd_diag_eq0=>P1. suff ->: svd_d A = 0 by rewrite linear0.
by apply/matrixP=>i j; rewrite !mxE ord1 P1// ?svd_pE// mul0rn.
Qed.

Lemma i2norm_ge0 m n (A : 'M[R]_(m,n)) : i2norm A >= 0.
Proof.
case: m A=>[A|m]. by rewrite i2norm_0n. case: n=>[A|n A]. by rewrite i2norm_n0.
by rewrite i2norm_Sn; apply/nnegmxP/svd_diag_nneg; rewrite svd_pE.
Qed.

Lemma i2norm_nneg m n (A : 'M[R]_(m,n)) : i2norm A \is Num.nneg.
Proof. by rewrite qualifE /Rnneg_pred i2norm_ge0. Qed.

Lemma i2normZ m n a (A : 'M[R]_(m,n)) : i2norm (a *: A) = `|a| * i2norm A.
Proof. 
case: m A=>[A|m]; first by rewrite !i2norm_0n mulr0.
case: n=>[A|n A]; first by rewrite !i2norm_n0 mulr0.
by rewrite !i2norm_Sn svd_dZ !mxE.
Qed.

Lemma i2norm0 m n : @i2norm m n 0 = 0.
Proof. by rewrite -(scale0r 0) i2normZ normr0 mul0r. Qed.

Lemma i2norm0P m n A : reflect (@i2norm m n A = 0) (A == 0).
Proof. by apply: (iffP eqP)=> [->|/i2norm0_eq0 //]; apply: i2norm0. Qed.

Definition i2norm_eq0 m n A := sameP (@i2norm m n A =P 0) (i2norm0P A).

Lemma l2norm_diag_mul n D p (M : 'M[R]_(n.+1,p)) : D \is is_svd_diag ->
  l2norm (diag_mx D *m M) <= D 0 0 * l2norm M.
Proof. 
move=>P1; move: {+}P1=>/is_svd_diagP/(_ 0) [P2 _].
rewrite -(ler_pXn2r (ltn0Sn 1)) ?nnegrE ?mulr_ge0 ?normv_ge0// exprMn 
  -!dot_l2norm /mxtrace mulr_sumr; apply ler_sum=> i _.
rewrite !dot_dotmxE row_diag_mul linearZl_LR linearZr_LR/= mulrA.
apply ler_pM=>//; rewrite -?normCK ?exprn_ge0// ?dnorm_ge0// 
  (ler_pXn2r (ltn0Sn 1)) ?nnegrE// ger0_norm ?svd_diag_ge0//.
by move/svd_diag_decreasing/is_decreasingP: P1=>/(_ 0 i)/=.
Qed.

Lemma l2norm_cdiag_mul m n p (D: 'rV[R]_(minn m.+1 n.+1)) 
  (M : 'M[R]_(n.+1,p)) : D \is is_svd_diag ->
  l2norm (cdiag_mx D *m M) <= D 0 c0 * l2norm M.
Proof.
move=>P1; move: {+}P1=>/is_svd_diagP/(_ c0) [P2 _].
rewrite -(ler_pXn2r (ltn0Sn 1)) ?nnegrE ?mulr_ge0 ?normv_ge0// exprMn 
  -!dot_l2norm adjmxM mulmxA mxtrace_mulC !mulmxA cdiag_mx_mulr -diag_mx_dmul
  svd_d_exdr_conj -diag_mx_adj mxtrace_mulC -mulmxA mulmxA -adjmxM mxtrace_mulC 
  /mxtrace mulr_sumr; apply ler_sum=> i _.
rewrite !dot_dotmxE row_diag_mul linearZl_LR linearZr_LR/= mulrA.
apply ler_pM=>//; rewrite -?normCK ?exprn_ge0// ?dnorm_ge0// (ler_pXn2r 
  (ltn0Sn 1)) ?nnegrE// ger0_norm ?svd_diag_ge0//; first by apply/svd_diag_exdr.
rewrite /svd_d_exdr castmxE ord1/=; set j := (cast_ord (esym (min_idr m.+1 n.+1)) i).
rewrite -(splitK j) mxE/=; case: (fintype.split (unsplit (fintype.split j)))=>a/=.
by move/svd_diag_decreasing/is_decreasingP: P1=>/(_ c0 a)/=. by rewrite mxE.
Qed.

Lemma i2norm_dotr m n p (M : 'M[R]_(m,n)) (N : 'M[R]_(n,p)): 
  l2norm (M *m N) <= i2norm M * l2norm N.
Proof.
case: n M N=>[M N|n]; last case: m=>[M N|m]; last case: p=>[M N|p M N].
1,2,3: by rewrite !mx_dim0E ?mulmx0 ?normv0 ?i2norm0 ?mul0r// mulr0.
rewrite i2norm_Sn {1}(svdE M) -!mulmxA l2normUl ?svd_pE//.
apply: (le_trans (l2norm_cdiag_mul _ _)); first by rewrite svd_pE.
by rewrite l2normUl// trmxC_unitary svd_pE.
Qed.

Lemma i2norm_dotl m n p (M : 'M[R]_(m,n)) (N : 'M[R]_(p,m)): 
  l2norm (N *m M) <= i2norm M * l2norm N.
Proof. by rewrite -l2norm_adjmx -[X in _ * X]l2norm_adjmx 
adjmxM -i2norm_adjmx i2norm_dotr. Qed.

Lemma diag_mx_deltaM m n i (j : 'I_n) (D : 'rV[R]_m) : 
  diag_mx D *m delta_mx i j = D 0 i *: delta_mx i j.
Proof. 
apply/matrixP=>a b. rewrite !mxE (bigD1 i)//= big1.
by move=>k /negPf nki; rewrite !mxE nki/= mulr0.
by rewrite addr0 !mxE eqxx/=; case: eqP=>[->|]; rewrite ?mulr1n//= mulr0n mulr0 mul0r.
Qed.

Lemma i2norm_existsr m n (M : 'M[R]_(m.+1,n.+1)) p : exists2 A : 'M[R]_(n.+1,p.+1), 
  (l2norm A = 1) & (l2norm (M *m A) = i2norm M). 
Proof.
exists (svd_v M *m delta_mx 0 0); last first.
rewrite {1}(svdE M) mulmxA mulmxKtV// ?svd_pE// -mulmxA l2normUl ?svd_pE//.
rewrite l2norm_dotV adjmxM -mulmxA [X in _ *m X]mulmxA cdiag_mx_mulr 
  -diag_mx_dmul svd_d_exdr_conj -diag_mx_adj -mulmxA mulmxA -adjmxM -l2norm_dotV 
  diag_mx_deltaM normvZ/= i2norm_Sn ger0_norm.
apply/nnegmxP/svd_diag_nneg/svd_diag_exdr/svd_d_svd_diag.
by rewrite l2norm_deltamx mulr1 svd_d_exdr0.
by rewrite l2normUl ?svd_pE// l2norm_deltamx.
Qed.

Lemma i2norm_existsl m n (M : 'M[R]_(m.+1,n.+1)) p : 
  exists2 A : 'M[R]_(p.+1,m.+1), (l2norm A = 1) & (l2norm (A *m M) = i2norm M). 
Proof.
move: (i2norm_existsr (M^*t) p)=>[A P1 P2].
exists (A^*t). by rewrite l2norm_adjmx.
by rewrite -[LHS]l2norm_adjmx !adjmxM adjmxK P2 i2norm_adjmx.
Qed.

Lemma i2norm_triangle m n (A B : 'M[R]_(m,n)) : 
  i2norm (A + B) <= i2norm A + i2norm B.
Proof.
case: m A B=>[A B|m]; last case: n=>[A B|n A B].
1,2: by rewrite ?i2norm_0n ?i2norm_n0 addr0.
move: (i2norm_existsr (A+B) 0)=>[c P1 P2]; rewrite -P2 mulmxDl.
apply (le_trans (l2norm_triangle _ _)).
by apply lerD; apply (le_trans (i2norm_dotr _ _)); rewrite P1 mulr1.
Qed.

Lemma i2norm1 n : i2norm (1%:M : 'M[R]_n.+1) = 1.
Proof. by rewrite i2norm_Sn svd_d_const mxE normr1. Qed.

Lemma i2norm_const n a : i2norm (a%:M : 'M[R]_n.+1) = `|a|.
Proof. by rewrite -scalemx1 i2normZ i2norm1 mulr1. Qed.

Lemma i2normUl m n (A : 'M[R]_(m,n)) (U : 'M[R]_m) : 
  U \is unitarymx -> i2norm (U *m A) = i2norm A.
Proof. by move=>UU; rewrite /i2norm; apply eq_bigr=>i _; rewrite svd_d_Ul. Qed.

Lemma i2normUr m n (A : 'M[R]_(m,n)) (U : 'M[R]_n) : 
  U \is unitarymx -> i2norm (A *m U) = i2norm A.
Proof. by move=>UU; rewrite /i2norm; apply eq_bigr=>i _; rewrite svd_d_Ur. Qed.

Lemma i2norm_unitary m n (U : 'M[R]_(m.+1,n.+1)) : 
  U \is unitarymx -> i2norm U = 1.
Proof. by move=>UU; rewrite i2norm_Sn svd_d_unitary ?mxE. Qed.

Lemma i2norm_l2norm m n (A : 'M[R]_(m,n)) : i2norm A <= l2norm A.
Proof.
case: m A=>[A|m]; last case: n =>[A|n A]. 1,2: by rewrite !mx_dim0E i2norm0 normv0.
rewrite i2norm_Sn {2}(svdE A) l2normUr ?trmxC_unitary ?svd_pE// l2normUl ?svd_pE//.
rewrite l2norm_dotV cdiag_mx_mulr -diag_mx_dmul svd_d_exdr_conj -diag_mx_adj -l2norm_dotV.
rewrite l2norm_diag -(ler_pXn2r (ltn0Sn 1)) ?nnegrE ?svd_d_ge0// ?normv_ge0//.
rewrite -svd_d_exdr0 /l2norm sqrtCK (bigD1 (0,0))//= ger0_norm.
apply/nnegmxP/svd_diag_nneg/svd_diag_exdr/svd_d_svd_diag.
apply ler_wpDr=>//. apply sumr_ge0=>i _. rewrite exprn_ge0//.
Qed.

Lemma i2normM m n p (A : 'M[R]_(m,n)) (B : 'M[R]_(n,p)) : 
  i2norm (A *m B) <= i2norm A * i2norm B.
Proof.
case: m A=>[A|m]; last case: p B=>[B A|p]; last case: n=>[B A|n B A].
1,2,3: by rewrite !mx_dim0E ?mulmx0 !i2norm0 ?mul0r ?mulr0.
move: (i2norm_existsr (A *m B) n)=>[C P1 <-].
rewrite -mulmxA. apply (le_trans (i2norm_dotr _ _)).
apply ler_pM=>//. apply i2norm_ge0. apply normv_ge0.
by apply (le_trans (i2norm_dotr _ _)); rewrite P1 mulr1.
Qed.

Lemma i2norm_elem m n (A : 'M[R]_(m,n)) : forall i j, `|A i j| <= i2norm A.
Proof.
move=>i j. suff ->: `|A i j| = l2norm ((delta_mx i i) *m A *m (delta_mx j j)).
apply (le_trans (i2norm_dotr _ _)). rewrite l2norm_deltamx mulr1.
apply (le_trans (i2normM _ _)). apply ler_piMl. apply i2norm_ge0.
apply (le_trans (i2norm_l2norm _)). by rewrite l2norm_deltamx.
rewrite /l2norm /pnorm (bigD1 (i,j))//= big1=>[d /pair_neq[P1|P1]|].
1: rewrite -mulmxA. 1,2: by rewrite !mxE big1 ?normr0 ?expr0n// =>k _; 
   rewrite !mxE P1/= ?andbF ?mulr0 ?mul0r.
rewrite mxE (bigD1 j)//= big1=>[k /negPf nkj|]; rewrite !mxE ?nkj/= ?mulr0// 
  (bigD1 i)//= big1=>[k /negPf nkj|]; rewrite !mxE ?nkj/= ?andbF ?mul0r//; 
  rewrite !eqxx/= !addr0 mulr1 mul1r sqrCK//.
Qed.

Lemma i2norm_svd m n (A : 'M[R]_(m,n)) : i2norm A = i2norm (cdiag_mx (svd_d A)).
Proof. by rewrite {1}[A]svdE i2normUr ?i2normUl// ?trmxC_unitary svd_pE. Qed.
Lemma i2norm_svds m (A : 'M[R]_m) : i2norm A = i2norm (diag_mx (svds_d A)).
Proof. by rewrite {1}[A]svdsE i2normUr ?i2normUl// ?trmxC_unitary svd_pE. Qed.

HB.instance Definition _ m n := isVNorm.Build R 'M_(m, n) (@i2norm m n)
  (@i2norm_triangle m n) (@i2norm0_eq0 m n) (@i2normZ m n).

End Induced2Norm.

(* 1. lemma about svd_d_exdr/l *)
(* 2. lemma about diag_mx svd_d_exdr/l *)
Lemma svd_d_exdr_dmul (T : numClosedFieldType) (p q : nat) (D D' : 'rV[T]_(minn p q)) :
  svd_d_exdr D .* svd_d_exdr D' = svd_d_exdr (D .* D').
Proof.
rewrite /svd_d_exdr; apply/matrixP=>i j.
by rewrite mxE !castmxE !mxE; case: split_ordP=>k _; rewrite mxE// mulr0.
Qed.

Lemma svd_d_exdl_dmul (T : numClosedFieldType) (p q : nat) (D D' : 'rV[T]_(minn p q)) :
  svd_d_exdl D .* svd_d_exdl D' = svd_d_exdl (D .* D').
Proof.
rewrite /svd_d_exdl; apply/matrixP=>i j.
by rewrite mxE !castmxE !mxE; case: split_ordP=>k _; rewrite mxE// mulr0.
Qed.

(* TODO : move, simplify schattennorm_exdr *)
Lemma pnorm_svd_d_exdr (T : numClosedFieldType) p (m n : nat) (D : 'rV[T]_(minn m n)) :
  pnorm p (svd_d_exdr D) = pnorm p D.
Proof.
rewrite !pnorm_pair !big_ord1; f_equal; symmetry.
apply (@svd_d_exd_sumr _ _ _ D (fun x=>`|x|^+p.+1)).
by rewrite normr0 expr0n.
Qed.

Lemma pnorm_svd_d_exdl (T : numClosedFieldType) p (m n : nat) (D : 'rV[T]_(minn m n)) :
  pnorm p (svd_d_exdl D) = pnorm p D.
Proof.
rewrite !pnorm_pair !big_ord1; f_equal; symmetry.
apply (@svd_d_exd_suml _ _ _ D (fun x=>`|x|^+p.+1)).
by rewrite normr0 expr0n.
Qed.

Section SchattenNorm.
Variable (R: numClosedFieldType) (p : nat).

Definition schattennorm m n (M : 'M[R]_(m,n)) := (pnorm p (svd_d M)).

Lemma schattennorm_exdr m n (M : 'M[R]_(m,n)) : 
  schattennorm M = (pnorm p (svd_d_exdr (svd_d M))).
Proof. by rewrite pnorm_svd_d_exdr. Qed.

Lemma schattennorm_exdl m n (M : 'M[R]_(m,n)) : 
  schattennorm M = (pnorm p (svd_d_exdl (svd_d M))).
Proof. by rewrite pnorm_svd_d_exdl. Qed.

Lemma schattennorms m (M : 'M[R]_m) : 
  schattennorm M = (pnorm p (svds_d M)).
Proof.
rewrite /schattennorm /svds_d.
move: (minn_id m) (minn_id m)=>/esym P1 P2.
rewrite (eq_irrelevance P2 (esym P1)). clear P2.
set t := svd_d M. destruct t.
case: (minn m m) / P1 f=>f. by rewrite castmx_id.
Qed.

Lemma schattennorm_adjmx m n (M : 'M[R]_(m,n)) : 
  schattennorm (M^*t) = schattennorm M.
Proof. 
rewrite /schattennorm svd_d_adjmx; move: (minnC m n)=>P. 
by case: (minn n m) / P; rewrite castmx_id.
Qed.

Lemma schattennorm_trmx m n (M : 'M[R]_(m,n)) : 
  schattennorm (M^T) = schattennorm M.
Proof. 
rewrite /schattennorm svd_d_trmx; move: (minnC m n)=>P. 
by case: (minn n m) / P; rewrite castmx_id.
Qed.

Lemma schattennorm_conjmx m n (M : 'M[R]_(m,n)) : 
  schattennorm (M^*m) = schattennorm M.
Proof. by rewrite -schattennorm_trmx -adjmxCT schattennorm_adjmx. Qed.

Lemma schattennorm0_eq0 m n (M : 'M[R]_(m,n)) : schattennorm M = 0 -> M = 0.
Proof.
rewrite /schattennorm=>/pnorm0_eq0.
rewrite {2}(svdE M)=>->. by rewrite linear0 mulmx0 mul0mx.
Qed.

Lemma schattennorm_ge0 m n (M : 'M[R]_(m,n)) : schattennorm M >= 0.
Proof. by rewrite /schattennorm pnorm_ge0. Qed.

Lemma schattennorm_nneg m n (M : 'M[R]_(m,n)) : schattennorm M \is Num.nneg.
Proof. by rewrite nnegrE schattennorm_ge0. Qed.

Lemma schattennormZ m n a (M : 'M[R]_(m,n)) : 
  schattennorm (a *: M) = `|a| * schattennorm M.
Proof. by rewrite /schattennorm svd_dZ pnormZ normr_id. Qed.

Lemma schattennorm0 m n : @schattennorm m n 0 = 0.
Proof. by rewrite -(scale0r 0) schattennormZ normr0 mul0r. Qed.

Lemma schattennorm0P m n A : reflect (@schattennorm m n A = 0) (A == 0).
Proof. by apply: (iffP eqP)=> [->|/schattennorm0_eq0 //]; apply: schattennorm0. Qed.

Definition schattennorm_eq0 m n A := sameP (@schattennorm m n A =P 0) (schattennorm0P A).

Lemma schattennormUl m n (M : 'M[R]_(m,n)) (U : 'M[R]_m) : 
  U \is unitarymx -> schattennorm (U *m M) = schattennorm M.
Proof. by move=>UU; rewrite /schattennorm svd_d_Ul. Qed.

Lemma schattennormUr m n (M : 'M[R]_(m,n)) (U : 'M[R]_n) : 
  U \is unitarymx -> schattennorm (M *m U) = schattennorm M.
Proof. by move=>UU; rewrite /schattennorm svd_d_Ur. Qed.

Lemma schattennorm_svd m n (M : 'M[R]_(m,n)) :
  schattennorm M = schattennorm (cdiag_mx (svd_d M)).
Proof. by rewrite {1}[M]svdE schattennormUr ?schattennormUl// ?trmxC_unitary svd_pE. Qed.

Lemma schattennorm_svds m (M : 'M[R]_(m)) :
  schattennorm M = schattennorm (diag_mx (svds_d M)).
Proof. by rewrite {1}[M]svdsE schattennormUr ?schattennormUl// ?trmxC_unitary svd_pE. Qed.

End SchattenNorm.

Definition fbnorm (R: numClosedFieldType) := (@schattennorm R 1).
Definition trnorm (R: numClosedFieldType) := (@schattennorm R 0).
Notation "\fb| M |" := (fbnorm M).
Notation "\tr| M |" := (trnorm M).

Section fbtrnorm_inherited.
Variable (R: numClosedFieldType) (m n : nat) (M : 'M[R]_(m,n)).

Lemma fbnorm_adjmx : \fb| M^*t | = \fb| M |. Proof. exact: schattennorm_adjmx. Qed.
Lemma fbnorm_conjmx : \fb| M^*m | = \fb| M |. Proof. exact: schattennorm_conjmx. Qed.
Lemma fbnorm_trmx : \fb| M^T | = \fb| M |. Proof. exact: schattennorm_trmx. Qed.
Lemma fbnorm0_eq0 : \fb| M | = 0 -> M = 0. Proof. exact: schattennorm0_eq0. Qed.
Lemma fbnorm_ge0  : \fb| M | >= 0.         Proof. exact: schattennorm_ge0. Qed.
Lemma fbnorm_nneg : \fb| M | \is Num.nneg. Proof. exact: schattennorm_nneg. Qed.
Lemma fbnorm0     : \fb| (0 : 'M[R]_(m,n)) | = 0.    Proof. exact: schattennorm0. Qed.
Lemma fbnorm0P    : reflect (\fb| M | = 0) (M == 0). Proof. exact: schattennorm0P. Qed.
Definition fbnorm_eq0 := sameP (\fb| M | =P 0) (fbnorm0P).
Lemma fbnormZ a (N : 'M[R]_(m,n))  : \fb| a *: N | = `|a| * \fb| N |. 
Proof. exact: schattennormZ. Qed.
Lemma fbnormUl (U : 'M[R]_m) : U \is unitarymx -> \fb| U *m M | = \fb| M |.
Proof. exact: schattennormUl. Qed.
Lemma fbnormUr (U : 'M[R]_n) : U \is unitarymx -> \fb| M *m U | = \fb| M |.
Proof. exact: schattennormUr. Qed.
Lemma fbnorm_svd : \fb| M | = \fb| cdiag_mx (svd_d M) |.
Proof. exact: schattennorm_svd. Qed.
Lemma fbnorm_svds (N : 'M[R]_m) : \fb| N | = \fb| diag_mx (svds_d N) |.
Proof. exact: schattennorm_svds. Qed.

Lemma trnorm_adjmx : \tr| M^*t | = \tr| M |. Proof. exact: schattennorm_adjmx. Qed.
Lemma trnorm_conjmx : \tr| M^*m | = \tr| M |. Proof. exact: schattennorm_conjmx. Qed.
Lemma trnorm_trmx : \tr| M^T | = \tr| M |. Proof. exact: schattennorm_trmx. Qed.
Lemma trnorm0_eq0 : \tr| M | = 0 -> M = 0. Proof. exact: schattennorm0_eq0. Qed.
Lemma trnorm_ge0  : \tr| M | >= 0.         Proof. exact: schattennorm_ge0. Qed.
Lemma trnorm_nneg : \tr| M | \is Num.nneg. Proof. exact: schattennorm_nneg. Qed.
Lemma trnorm0     : \tr| (0 : 'M[R]_(m,n)) | = 0.    Proof. exact: schattennorm0. Qed.
Lemma trnorm0P    : reflect (\tr| M | = 0) (M == 0). Proof. exact: schattennorm0P. Qed.
Definition trnorm_eq0 := sameP (\tr| M | =P 0) (trnorm0P).
Lemma trnormZ a (N : 'M[R]_(m,n))  : \tr| a *: N | = `|a| * \tr| N |. 
Proof. exact: schattennormZ. Qed.
Lemma trnormUl (U : 'M[R]_m) : U \is unitarymx -> \tr| U *m M | = \tr| M |.
Proof. exact: schattennormUl. Qed.
Lemma trnormUr (U : 'M[R]_n) : U \is unitarymx -> \tr| M *m U | = \tr| M |.
Proof. exact: schattennormUr. Qed.
Lemma trnorm_svd : \tr| M | = \tr| cdiag_mx (svd_d M) |.
Proof. exact: schattennorm_svd. Qed.
Lemma trnorm_svds (N : 'M[R]_m) : \tr| N | = \tr| diag_mx (svds_d N) |.
Proof. exact: schattennorm_svds. Qed.

End fbtrnorm_inherited.

Section FrobeniusNorm.
Variable (R: numClosedFieldType).

Lemma fbnorm_l2norm m n (M : 'M[R]_(m,n)) :
  fbnorm M = l2norm M.
Proof.
by rewrite/fbnorm /schattennorm {2}[M]svdE l2normUr 
  ?trmxC_unitary ?svd_pE// l2normUl ?svd_pE// /l2norm pnorm_cdiag.
Qed.

Lemma fbnorm_trnormV m n (M : 'M[R]_(m,n)) :
  \fb| M | = sqrtC (\tr (M^*t *m M)).
Proof. by rewrite dotV_l2norm fbnorm_l2norm sqrtCK. Qed.

Lemma fbnorm_trnorm m n (M : 'M[R]_(m,n)) :
  \fb| M | = sqrtC (\tr (M *m M^*t)).
Proof. by rewrite dot_l2norm fbnorm_l2norm sqrtCK. Qed.

Lemma fbnorm_dotr m n p (M : 'M[R]_(m,n)) (N : 'M[R]_(n,p)): 
  l2norm (M *m N) <= fbnorm M * i2norm N.
Proof.
case: m M=>[M|m M]; last case: p N=>[N|p N]; last case: n M N=>[M N|n M N].
1,2,3: by rewrite !mx_dim0E ?mulmx0 ?normv0 ?fbnorm0 ?mul0r// mulr0.
apply (le_trans (i2norm_dotl _ _)).
by rewrite mulrC ler_pM// ?normv_ge0// /fbnorm {1}(svdE M) 
  l2normUr ?trmxC_unitary ?l2normUl ?svd_pE// l2norm_cdiag.
Qed.

Lemma fbnorm_dotl m n p (M : 'M[R]_(m,n)) (N : 'M[R]_(p,m)) : 
  l2norm (N *m M) <= fbnorm M * i2norm N.
Proof. by rewrite -l2norm_adjmx -fbnorm_adjmx -i2norm_adjmx adjmxM fbnorm_dotr. Qed.

Lemma fbnorm_existsr m n (M: 'M[R]_(m.+1,n.+1)) : exists2 A : 'M[R]_(n.+1),
  (i2norm A = 1) & (l2norm (M *m A) = fbnorm M).
Proof.
exists (svd_v M). by rewrite i2norm_unitary// svd_pE.
by rewrite {1}(svdE M) mulmxKtV// ?svd_pE// l2normUl ?svd_pE// l2norm_cdiag.
Qed.

Lemma fbnorm_existsl m n (M: 'M[R]_(m.+1,n.+1)) : exists2 A : 'M[R]_(m.+1),
  (i2norm A = 1) & (l2norm (A *m M) = fbnorm M).
Proof.
by move: (fbnorm_existsr (M^*t))=>[A P1 P2]; exists (A^*t); 
  rewrite ?i2norm_adjmx// -l2norm_adjmx adjmxM adjmxK P2 fbnorm_adjmx.
Qed.

Lemma fbnorm_triangle m n (x y: 'M[R]_(m,n)) : \fb| x + y | <= \fb| x | + \fb| y |.
Proof. by rewrite !fbnorm_l2norm lev_normD. Qed.

Lemma fbnormM m n p (x : 'M[R]_(m,n)) (y: 'M[R]_(n,p)) :
  \fb| x *m y | <= \fb| x | * \fb| y |.
Proof.
rewrite -(ler_pXn2r (ltn0Sn 1)) ?nnegrE ?mulr_ge0 ?fbnorm_ge0// !fbnorm_l2norm
  -(l2norm_trmx y) /l2norm !pnorm_pair exprMn !sqrtCK mulr_suml;
under [X in _ <= X]eq_bigr do rewrite mulr_sumr.
apply: ler_sum=> i _; apply: ler_sum=> j _.
under [X in _ * X]eq_bigr do rewrite mxE;
rewrite mxE; exact: Cauchy_Schwarz_C.
Qed.

Lemma fbnormMl m n p (x : 'M[R]_(m,n)) (y: 'M[R]_(n,p)) : 
  fbnorm (x *m y) <= fbnorm x * i2norm y.
Proof.
case: m x y=>[x y|m]; last case: p=>[x y|p]; last case: n=>[x y|n x y].
1,2,3: by rewrite !mx_dim0E ?mulmx0 ?i2norm0 ?fbnorm0 ?mulr0// mul0r.
move: (fbnorm_existsr (x*m y))=>[A PA <-].
rewrite -mulmxA. apply (le_trans (fbnorm_dotr _ _)).
apply ler_pM=>//. apply schattennorm_ge0. apply i2norm_ge0.
by apply (le_trans (i2normM _ _)); rewrite PA mulr1.
Qed.

Lemma fbnormMr m n p (x : 'M[R]_(m,n)) (y: 'M[R]_(n,p)) : 
  fbnorm (x *m y) <= i2norm x * fbnorm y.
Proof.
rewrite -fbnorm_adjmx adjmxM; apply: (le_trans (fbnormMl _ _)).
by rewrite mulrC i2norm_adjmx fbnorm_adjmx.
Qed.

(* TODO : generalize to all pnorm and schattennorm *)
Lemma fbnormMV m n (x : 'M[R]_(m,n)) :
  \fb| x^*t *m x | = \fb| x *m x^*t |.
Proof.
rewrite (svdE x) !adjmxM !adjmxK -!mulmxA !fbnormUl ?mulmxA ?fbnormUr
  ?trmxC_unitary ?svd_u_unitarymx ?svd_v_unitarymx// !mulmxACA
  (unitarymxPV _ (svd_u_unitarymx x)) (unitarymxPV _ (svd_v_unitarymx x))
  !mulmx1 cdiag_mx_mull cdiag_mx_mulr /= !fbnorm_l2norm /l2norm !pnorm_diag.
by rewrite dmulmxC svd_d_exdr_dmul pnorm_svd_d_exdr svd_d_exdl_dmul pnorm_svd_d_exdl.
Qed.

Lemma i2norm_fbnorm m n (M : 'M[R]_(m,n)) : i2norm M <= fbnorm M.
Proof.
case: m M=>[M|m]; last case: n=>[M|n M]. 1,2: by rewrite !mx_dim0E i2norm0 fbnorm0.
rewrite -(ler_pXn2r (ltn0Sn 1)) ?nnegrE ?i2norm_ge0// ?schattennorm_ge0//.
rewrite i2norm_Sn /fbnorm /schattennorm pnorm_pair big_ord1 sqrtCK (bigD1 (c0 _ _))//= 
  ger0_norm ?svd_d_ge0// ler_wpDr=>//. apply sumr_ge0=>i _. rewrite exprn_ge0//.
Qed.

HB.instance Definition _ m n := isVNorm.Build R 'M_(m, n) (@fbnorm R m n)
  (@fbnorm_triangle m n) (@fbnorm0_eq0 _ m n) (@fbnormZ _ m n).

End FrobeniusNorm.

(* also know as nuclear norm *)
Section TraceNorm.
Variable (R: numClosedFieldType).

Definition i1fun m n (M N: 'M[R]_(m,n)) := `|\tr(M ^*t *m N)|.

Lemma i1funA m n p (M : 'M[R]_(m,n)) (N: 'M_(m,p)) (N': 'M_(p,n)) : 
  i1fun M (N *m N') = i1fun (M *m N'^*t) N.
Proof. by rewrite /i1fun adjmxM adjmxK mulmxA mxtrace_mulC mulmxA. Qed.

Lemma i1fun_triangle m n (M N N': 'M[R]_(m,n)) : 
  i1fun M (N + N') <= i1fun M N + i1fun M N'.
Proof. by rewrite /i1fun mulmxDr linearD/= ler_normD. Qed.

Lemma trnorm_svdE m n (M: 'M[R]_(m,n)) : \tr| M | = \sum_i svd_d M 0 i.
Proof.
rewrite /trnorm /schattennorm pnorm_pair root1C big_ord1.
by apply eq_bigr=>i _; rewrite expr1 ger0_norm// svd_d_ge0.
Qed.

Lemma tr_mul_diag m n (M: 'M[R]_(n,m)) (D: 'rV[R]_(minn m n)) : 
\tr (M *m cdiag_mx D) = \sum_(i < minn m n) D 0 i *
M (cast_ord (min_idr m n) (lshift _ i)) (cast_ord (min_idl m n) (lshift _ i)).
Proof.
move: (min_idl m n) (min_idr m n)=>P1 P2. 
rewrite /mxtrace (big_ord_cast P2) big_split_ord/= [X in _ + X]big1 ?addr0=>[i _|].
1: rewrite mxE big1// =>k _. 2: apply eq_bigr=>i _; rewrite mxE (big_ord_cast P1)/= 
  big_split_ord/= [X in _ + X]big1=>[k _|]; last rewrite (bigD1 i)//= big1=>[k/negPf nk|].
all: by rewrite /cdiag_mx castmxE !cast_ord_comp/= !cast_ord_id ?block_mxEul ?block_mxEur 
  ?block_mxEdl ?block_mxEdr ?block_mxEh ?row_mxEr ?col_mx0 mxE ?nk ?mulr0n ?mulr0//
  eqxx mulr1n !addr0 mulrC.
Qed.

Lemma trnorm_i1funr m n (M N: 'M[R]_(m.+1,n.+1)) : i1fun N M <= trnorm M * i2norm N.
Proof.
rewrite /i1fun {1}(svdE M) !mulmxA mxtrace_mulC !mulmxA tr_mul_diag.
apply/(le_trans (ler_norm_sum _ _ _))/(@le_trans _ _ (\sum_i i2norm N * svd_d M 0 i)).
apply ler_sum=>i _; rewrite normrM mulrC ler_pM=>//.
by apply (le_trans (i2norm_elem _ _ _)); rewrite i2normUr ?svd_pE// i2normUl 
  ?trmxC_unitary ?svd_pE// i2norm_adjmx. by rewrite ger0_norm// svd_d_ge0.
by rewrite -mulr_sumr mulrC trnorm_svdE.
Qed.

Lemma trnorm_existsr m n (M: 'M[R]_(m.+1,n.+1)) : exists2 A : 'M[R]_(m.+1,n.+1),
  (i2norm A = 1) & (i1fun A M = trnorm M).
Proof.
exists (svd_u M *m cdiag_mx (const_mx 1) *m (svd_v M)^*t).
rewrite i2normUr ?trmxC_unitary ?i2normUl ?svd_pE// i2norm_Sn svd_cdiagmx.
by apply/const_svd_diag/ler01. by rewrite mxE.
rewrite /i1fun {3}(svdE M) !adjmxM -!mulmxA mxtrace_mulC !mulmxA adjmxK !mulmxKtV//
  ?svd_pE// cdiag_mx_mulr mxtrace_diag /trnorm schattennorm_exdr pnorm_pair root1C 
  big_ord1 ger0_norm ?sumr_ge0// =>[k _|].
2: apply eq_bigr=>k _; rewrite expr1 ger0_norm ?mxE.
2: apply/nnegmxP/svd_diag_nneg/svd_diag_exdr/svd_d_svd_diag.
all: by rewrite ?mxE /svd_d_exdr !castmxE !ord1/=;
  set t:= unkeyed (cast_ord (esym (min_idr m.+1 n.+1)) k);
  rewrite -(splitK t); case: (fintype.split t)=>a/=;
  rewrite ?row_mxEl ?row_mxEr !mxE ?mulr0// conjC1 mul1r// svd_d_ge0.
Qed.

Lemma trnorm_triangle m n (x y: 'M[R]_(m,n)) : \tr| x + y | <= \tr| x | + \tr| y |.
Proof.
case: n x y=>[x y|n x y]; last case: m x y=>[x y|m x y].
1,2: by rewrite !mx_dim0E !trnorm0 addr0.
move: (trnorm_existsr (x+y))=>[A P1 <-].
apply (le_trans (i1fun_triangle _ _ _ )). 
by apply lerD; apply (le_trans (trnorm_i1funr _ _)); rewrite P1 mulr1.
Qed.

Lemma trnormMl m n p (x : 'M[R]_(m,n)) (y : 'M[R]_(n,p)) : 
  trnorm (x *m y) <= trnorm x * i2norm y.
Proof.
case: m x y=>[x y|m]; last case: p=>[x y|p]; last case: n=>[x y|n x y].
1,2,3: by rewrite !mx_dim0E ?mulmx0 ?i2norm0 ?trnorm0 ?mulr0// mul0r.
move: (trnorm_existsr (x*m y))=>[A PA <-].
rewrite i1funA. apply (le_trans (trnorm_i1funr _ _)).
apply ler_pM=>//. apply trnorm_ge0. apply i2norm_ge0.
by apply (le_trans (i2normM _ _)); rewrite PA mul1r i2norm_adjmx.
Qed.

Lemma trnormMr m n p (x : 'M[R]_(m,n)) (y : 'M[R]_(n,p)) : 
  trnorm (x *m y) <= i2norm x * trnorm y.
Proof.
rewrite -trnorm_adjmx adjmxM; apply: (le_trans (trnormMl _ _)).
by rewrite mulrC i2norm_adjmx trnorm_adjmx.
Qed.

Lemma i2norm_trnorm m n (M : 'M[R]_(m,n)) : i2norm M <= trnorm M.
Proof.
case: m M=>[M|m]; last case: n=>[M|n M]. 1,2: by rewrite !mx_dim0E i2norm0 trnorm0.
rewrite i2norm_Sn trnorm_svdE (bigD1 (c0 _ _))//=. rewrite lerDl.
apply sumr_ge0=>i _. apply svd_d_ge0.
Qed.

Lemma trnorm_ge_tr n (M : 'M[R]_n) : `| \tr M | <= trnorm M.
Proof.
rewrite {1}(svdE M) mxtrace_mulC mulmxA tr_mul_diag trnorm_svdE.
apply: (le_trans (ler_norm_sum _ _ _)).
apply ler_sum=>i _. rewrite normrM [X in X * _]ger0_norm ?svd_d_ge0//.
apply ler_piMr. apply svd_d_ge0. 
apply: (le_trans (i2norm_elem _ _ _)).
case: n M i=>[M i|n M i]; first by rewrite i2norm_n0 ler01.
by rewrite i2norm_unitary// unitarymx_mulmx_closed// ?trmxC_unitary svd_pE.
Qed.

(* Lemma foob n (M N : 'M[R]_n) : trnorm (M *m N) <= i2norm M * trnorm N.*)

(* Lemma trnorm_diag n (D : 'rV[R]_n) : trnorm (diag_mx D) = \sum_i `|D 0 i|. *)

Lemma psdmx_trnorm n (M : 'M[R]_n) : M \is psdmx -> \tr| M | = \tr M.
Proof.
move/psdmx_svd=>[psvd]. destruct psvd=>/= /and3P[P1 P2 /eqP P3].
rewrite P3 -mulmxA mxtrace_mulC mulmxtVK// trnormUl ?trmxC_unitary// trnormUr//.
rewrite /trnorm schattennorms svds_diagmx// pnorm_pair root1C big_ord1 mxtrace_diag.
apply eq_bigr=>i _. rewrite expr1 ger0_norm//. by apply/nnegmxP/svd_diag_nneg.
Qed.

Lemma trnorm_inner n p (M : 'M[R]_n) (N : 'M[R]_(n,p)) : 
  `| \tr (N^*t *m M *m N ) | <= \tr| M | * \tr(N^*t *m N ).
Proof.
rewrite mxtrace_mulC mulmxA mxtrace_mulC.
apply (le_trans (trnorm_ge_tr _)).
apply (le_trans (trnormMl _ _)).
apply ler_pM=>//. apply schattennorm_ge0. apply i2norm_ge0.
apply (le_trans (i2norm_trnorm _)).
by rewrite [X in _ <= X]mxtrace_mulC psdmx_trnorm// form_psd.
Qed.

Lemma form_tr_ge0 n m (A : 'M[R]_(m,n)) : 0 <= \tr (A *m A^*t ).
Proof. by rewrite dot_l2norm exprn_ge0// pnorm_ge0. Qed.

Lemma form_tr_eq0 n m (A : 'M[R]_(m,n)) : \tr (A *m A^*t ) = 0 -> A = 0.
Proof. by move/eqP; rewrite dot_l2norm sqrf_eq0=>/eqP; apply pnorm0_eq0. Qed.

Lemma formV_tr_ge0 n m (A : 'M[R]_(m,n)) : 0 <= \tr (A^*t *m A ).
Proof. by rewrite mxtrace_mulC form_tr_ge0. Qed.

Lemma formV_tr_eq0 n m (A : 'M[R]_(m,n)) : \tr (A^*t *m A ) = 0 -> A = 0.
Proof. rewrite mxtrace_mulC; exact: form_tr_eq0. Qed.

HB.instance Definition _ m n := isVNorm.Build R 'M_(m, n) _
  (@trnorm_triangle m n) (@trnorm0_eq0 _ m n) (@trnormZ _ m n).

End TraceNorm.

(****************************************************************************)
(* lowner order over 'M[R]_n as partial order, A <= B iff B - A \is psdmx   *)
(****************************************************************************)
Module MxLownerOrder.

Section LownerPOrder.
Variable (C : numClosedFieldType).
Definition lownerle n (M N : 'M[C]_n) := (N - M) \is psdmx.
(* Definition lownerlt n (M N : 'M[C]_n) := (N != M) && (lownerle M N). *)

(* Lemma lownerlt_def n (x y : 'M[C]_n): lownerlt x y = (y != x) && (lownerle x y).
Proof. by rewrite /lownerlt. Qed. *)

Lemma lownerle_anti n : antisymmetric (@lownerle n).
Proof. move=>x y /andP.
rewrite /lownerle -[y - x]opprB=> [[H1 H2]].
apply subr0_eq. by apply: (psdmx_eq0 H2 H1).
Qed.

Lemma lownerle_refl n : reflexive (@lownerle n).
Proof. move=>x. rewrite /lownerle addrN. apply psdmx0. Qed.

Lemma lownerle_trans n : transitive (@lownerle n).
Proof. 
move=>x y z; rewrite /lownerle => P1 P2.
move: (psdmx_add P2 P1); by rewrite addrA addrNK.
Qed.

(* Fact vorder_display : unit. Proof. exact: tt. Qed. *)
(* why using vorder_display fails to use <=? *)
HB.instance Definition _ n := Order.Le_isPOrder.Build ring_display 'M[C]_n
  (@lownerle_refl n) (@lownerle_anti n) (@lownerle_trans n).
(* HB.instance Definition _ n := Order.isPOrder.Build ring_display 'M[C]_n
  (@lownerlt_def n) (@lownerle_refl n) (@lownerle_anti n) (@lownerle_trans n). *)

HB.instance Definition _ n := [SubChoice_isSubPOrder of 'MDen[C]_n by <: with ring_display].

(* HB.instance Definition _ n : Order.SubPOrder ring_display _ := [POrder of 'MDen[C]_n by <:]. *)

Lemma le_lownerE n (x y : 'M[C]_n) : x ⊑ y = ((y - x) \is psdmx).
Proof. by rewrite /@Order.le/= /lownerle. Qed.

Lemma lemx_add2rP n (z x y : 'M[C]_n) : x ⊑ y -> x + z ⊑ y + z.
Proof. by rewrite !le_lownerE opprD addrACA addrN addr0. Qed.

Lemma lemx_pscale2lP n (e : C) (x y : 'M[C]_n) : 0 < e -> x ⊑ y -> e *: x ⊑ e *: y.
Proof.
rewrite !le_lownerE -scalerBr. set z := y - x.
move=>P1 /psdmx_dot P2. apply/psdmx_dot=>u. move: (P2 u).
rewrite linearZ/= -scalemxAl linearZ/= !nnegrE=>P3.
apply: (mulr_ge0 _ P3). by apply/ltW.
Qed.

HB.instance Definition _ n := POrderedLmodule_isVOrder.Build C 'M[C]_n (@lemx_add2rP n) (@lemx_pscale2lP n).

Lemma pscalemx_lge0 n (x : 'M[C]_n) (a : C) : 
  (0 : 'M[C]_n) ⊏ x -> (0 : 'M[C]_n) ⊑ a *: x = (0 <= a).
Proof.
move=>xgt0. apply/Bool.eq_iff_eq_true; split; last first.
by move=>age0; apply: scalev_ge0=>//; apply/ltW.
move: xgt0. rewrite lt_def {1 2}/Order.le/= /lownerle !subr0=>/andP[nx0 px] /psdmx_trnorm pz.
move: (trnorm_ge0 (a *: x)). rewrite pz linearZ/= pmulr_lge0//.
by rewrite lt_def -!psdmx_trnorm// trnorm_eq0 trnorm_ge0 nx0.
Qed.

HB.instance Definition _ n := VOrder_isCan.Build C 'M[C]_n (@pscalemx_lge0 n).

Lemma lemx_adj n (M N : 'M_n) : M^*t ⊑ N^*t = (M ⊑ N).
Proof. by rewrite !le_lownerE -linearB/= psdmx_adj. Qed.

Lemma lemx_conj n (M N : 'M_n) : M^*m ⊑ N^*m = (M ⊑ N).
Proof. by rewrite !le_lownerE -linearB/= psdmx_conj. Qed.

Lemma lemx_tr n (M N : 'M_n) : M^T ⊑ N^T = (M ⊑ N).
Proof. by rewrite !le_lownerE -linearB/= psdmx_tr. Qed.

End LownerPOrder.
End MxLownerOrder.
Import MxLownerOrder.

Section DecPsdmx.
Variable (R: numClosedFieldType).

Lemma nneg_form m (U : 'M[R]_m) (D:'rV_m) :
  D \is a nnegmx -> U *m diag_mx D *m U^*t \is psdmx.
Proof.
move/nnegmxP=> P1; apply/psdmx_dot=>u.
rewrite -{1}(adjmxK U) !mulmxA -adjmxM -mulmxA mx_dot_diag_mx nnegrE sumr_ge0// =>i _.
by rewrite mulr_ge0 ?exprn_ge0// -nnegrE P1.
Qed.

Lemma hermmx_psd_decomp m (M : 'M[R]_m) :
  M \is hermmx -> exists (M1 M2 : 'M[R]_m), M1 \is psdmx /\
  M2 \is psdmx /\ M1 - M2 = M.
Proof.
move=>Ph. move: {+}Ph=>/hermmx_normal/eigen_dec P0.
move: {+}Ph=>/hermitian_spectral_diag_real P1.
set D1 := \matrix_(i,j) if (spectral_diag M i j) >= 0 then 
  (spectral_diag M i j) else 0.
set D2 := \matrix_(i,j) if ~~((spectral_diag M i j) >= 0) then 
  - (spectral_diag M i j) else 0.
have P2: D1 - D2 = spectral_diag M.
apply/matrixP=>i j. rewrite !mxE. case: (0 <= spectral_diag M i j)=>/=.
by rewrite subr0. by rewrite opprK add0r.
have P3: D1 \is a nnegmx. apply/nnegmxP=>i j. 
rewrite mxE. case E: (0 <= spectral_diag M i j)=>//=. by rewrite nnegrE.
have P4: D2 \is a nnegmx. apply/nnegmxP=>i j. 
rewrite mxE. case E: (0 <= spectral_diag M i j)=>/=. by rewrite nnegrE.
rewrite nnegrE oppr_ge0. move: P1=>/realmxP/(_ i j). by rewrite realE E.
exists (eigenmx M *m diag_mx D1 *m (eigenmx M)^*t).
exists (eigenmx M *m diag_mx D2 *m (eigenmx M)^*t).
do ?split. 1,2: by apply/nneg_form.
by rewrite [RHS]P0 -P2 linearB/= linearBr/= linearBl/=.
Qed.

Lemma reim_decomp (a b : R) :
  a = (a + b^*)/2%:R + 'i * (- 'i * (a - b^*)/2%:R) /\ 
  b = ((a + b^*)/2%:R)^* + 'i * (- 'i * (a - b^*)/2%:R)^*.
Proof.
rewrite -{3}(conjCK 'i) -rmorphM -rmorphD conjCi !mulrA mulrN -!expr2 sqrrN.
by rewrite  !sqrCi opprK !mulNr !mul1r -mulrDl -mulrBl opprB [a-_]addrC 
  [_+(b^*- _)]addrC !addrA addrK addrNK -!mulr2n -(mulr_natr a) mulfK
  ?pnatr_eq0// -(mulr_natr b^*) mulfK ?pnatr_eq0// conjCK.
Qed.

Lemma mx_herm_decomp m (M : 'M[R]_m) : 
  exists (M1 M2 : 'M[R]_m), M1 \is hermmx /\ M2 \is hermmx /\ M1 + 'i *: M2 = M.
Proof.
set M1 := \matrix_(i,j) ((M i j + (M j i)^*)/2%:R).
set M2 := \matrix_(i,j) ((- 'i * (M i j - (M j i)^*)/2%:R)).
exists M1. exists M2.
do ? split. 1,2: apply/hermmxP/matrixP=>i j; rewrite /M1 /M2 !mxE 
  !rmorphM -?conjCi ?conjCK ?conjCi 1 ?mulNr -?mulrN ?rmorphB ?rmorphD conjCK ?opprB;
  congr (_ * _). by rewrite addrC. 
1,2: by symmetry; apply/conj_Creal; rewrite realV realn.
apply/matrixP=>i j. rewrite !mxE. by move: (reim_decomp (M i j) (M j i))=>[ <-].
Qed.

Lemma mx_psd_decomp m (M : 'M[R]_m) :
  exists (M1 M2 M3 M4 : 'M[R]_m) , M1 \is psdmx /\ M2 \is psdmx 
  /\ M3 \is psdmx /\ M4 \is psdmx /\ M = M1 - M2 + 'i *: M3 - 'i *: M4.
Proof.
move: (mx_herm_decomp M)=>[N1 [N2 [/hermmx_psd_decomp [M1 [M2 [P1 [P2 P3]]]] 
  [/hermmx_psd_decomp [M3 [M4 [P4 [P5 P6]]]] P7]]]].
exists M1. exists M2. exists M3. exists M4.
do ? split=>//. by rewrite -P7 -P3 -P6 scalerBr addrA.
Qed.

Lemma psdmxZ m (A: 'M[R]_m) c :
  0 <= c -> A \is psdmx -> c *: A \is psdmx.
Proof.
move=>Pc /psdmx_dot PA. apply/psdmx_dot=>u.
by rewrite nnegrE -scalemxAr -scalemxAl linearZ/= mulr_ge0// -nnegrE PA.
Qed.

Lemma psdmx_eigen_ge0 m (A: 'M[R]_m) k :
  A \is psdmx -> eigenval A k >= 0.
Proof. by move=>/psdmxP[_ /nnegmxP/(_ 0 k)]; rewrite nnegrE. Qed.

Lemma diag_decomp_absorb m (A: 'M[R]_m) : A \is psdmx -> 
  let v k := (sqrtC (eigenval A k) *: eigenvec A k) in 
    A = \sum_k (v k) *m (v k)^*t.
Proof.
move=>P/=. move: {+}P=>/psdmx_herm/hermmx_normal/eigen_sum{1}->.
apply eq_bigr=>i _. rewrite adjmxZ -scalemxAr -!scalemxAl scalerA -normCKC ger0_norm ?sqrtCK//.
by rewrite sqrtC_ge0; apply psdmx_eigen_ge0.
Qed.

Lemma le_lownerE_psdtr m (A B: 'M[R]_m) : 
  reflect (forall x, x \is psdmx -> \tr (A *m x) <= \tr (B *m x)) (A ⊑ B).
Proof.
rewrite le_lownerE. 
apply/(iffP (@psdmx_dot _ _ _))=>[P x /diag_decomp_absorb ->|P x].
rewrite !mulmx_sumr !linear_sum/= ler_sum // => i _.
by rewrite -subr_ge0 -linearB -mulmxBl/= mulmxA mxtrace_mulC -nnegrE mulmxA P.
rewrite -mulmxA mxtrace_mulC -mulmxA nnegrE mulmxBl linearB/= subr_ge0.
apply P. apply form_psd.
Qed.

Lemma le_lownerE_dentr m (A B: 'M[R]_m) : 
  reflect (forall x, x \is denmx -> \tr (A *m x) <= \tr (B *m x)) (A ⊑ B).
Proof.
apply/(iffP (@le_lownerE_psdtr _ _ _))=>H x Px.
apply H. by apply/denmx_psd.
case E: (x == 0). move/eqP: E=>->. by rewrite !linear0.
have P: \tr| x| != 0 by rewrite trnorm_eq0 E.
have : (\tr| x |)^-1 *: x \is denmx. apply/denmxP. split. 
apply psdmxZ=>//. by rewrite invr_ge0 trnorm_ge0.
by rewrite linearZ/= -(psdmx_trnorm Px)  mulVf.
move=>/H. rewrite -!scalemxAr !linearZ/= mulrC [_^-1*_]mulrC ler_pdivrMr.
by rewrite lt_def P trnorm_ge0. by rewrite mulrVK// unitfE.
Qed.

End DecPsdmx.

