(* -------------------------------------------------------------------- *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra perm fingroup.
From mathcomp.analysis Require Import -(notations)forms.
From mathcomp.real_closed Require Import mxtens.
Require Import notation mcaextra mcextra spectral.

(* -------------------------------------------------------------------- *)
Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

(* -------------------------------------------------------------------- *)
Local Open Scope ring_scope.

Import Order.Theory GRing.Theory Num.Theory Num.Def.

(******************************************************************************)
(*                 Predicate of matrix & Vector Norm/Order                    *)
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
(* -------------------------------------------------------------------------- *)
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
(* -------------------------------------------------------------------------- *)
(* Defining Types                                                             *)
(* 'MR[R]_(m,n) : subtype of realmx, closed under unitring                    *)
(* 'MH[R]_m     : subtype of hermmx, closed under lmod                        *)
(* 'MDen[R]_m   : subtype of denmx                                            *)
(* 'MObs[R]_m   : subtype of obsmx                                            *)
(* psdmx : closed under addr                                                  *)
(* unitarymx : closed under *m                                                *)
(* -------------------------------------------------------------------------- *)
(*         vnorm R T == interface type of function f : T -> R satisfying      *)
(*                      vector norm property, over R : numDomainType          *)
(*                      and T : lmodType                                      *)
(*                      The HB class is VNorm                                 *)
(*  porderLmodType R == join of porderType and lmodType (R : ringType)        *)
(*                      The HB class is POrderedLmodule                       *)
(*      vorderType R == interface type of lmodType (R : numDomainType)        *)
(*                      equipped with a vector order                          *)
(*                      The HB class is VOrder                                *)
(* -------------------------------------------------------------------------- *)
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

Lemma row_idem R m n (M : 'M[R]_(m,n)) i : row 0 (row i M) = row i M.
Proof. by apply/matrixP=>j k; rewrite !mxE. Qed.

Lemma linear_tensmx (R: comRingType) m n p q M : linear (@tensmx R m n p q M).
Proof.
move=>c A B/=; apply/matrixP=>i j; 
by rewrite !mxE mulrDr mulrA [_ * c]mulrC mulrA.
Qed.

Lemma linear_tensmxr (R: comRingType) m n p q M : linear ((@tensmx R m n p q)^~ M).
Proof. move=>c A B/=; apply/matrixP=>i j; by rewrite !mxE mulrDl mulrA. Qed.

HB.instance Definition _ (R: comRingType) m n p q := bilinear_isBilinear.Build 
  R 'M[R]_(m,n) 'M[R]_(p,q) 'M[R]_(m * p, n * q) *:%R *:%R 
  (@tensmx R m n p q) (@linear_tensmxr R m n p q, @linear_tensmx R m n p q).

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

Lemma adj_row' {m n : nat} (M : 'M[R]_(m, n)) i :
  (row' i M)^*t = col' i M^*t.
Proof. by rewrite adjmxE tr_row' map_col'. Qed.

Lemma adj_col' {m n : nat} (M : 'M[R]_(m, n)) i :
  (col' i M)^*t = row' i M^*t.
Proof. by rewrite adjmxE tr_col' map_row'. Qed. 

Lemma adjmx_col'' [m n] j (A : 'M[R]_(m,n.-1)) v :
  (col'' j A v)^*t = row'' j A^*t v^*t.
Proof. by rewrite adjmxE tr_col'' map_row''. Qed.

Lemma adjmx_row'' [m n] j (A : 'M[R]_(m.-1,n)) v :
  (row'' j A v)^*t = col'' j A^*t v^*t.
Proof. by rewrite adjmxE tr_row'' map_col''. Qed.

Lemma adj_block_mx m n k l (A : 'M[R]_(m,n)) B C (D : 'M_(k,l)) :
  (block_mx A B C D)^*t = block_mx A^*t C^*t B^*t D^*t.
Proof. by rewrite adjmxE tr_block_mx map_block_mx -!adjmxE. Qed.

Lemma mxrank_adj [m n] (M : 'M[R]_(m, n)) :
  \rank M^*t = \rank M.
Proof. by rewrite mxrank_map mxrank_tr. Qed.

Lemma mxrank_conj [m n] (A : 'M[R]_(m,n)) :
  \rank (A^*m) = \rank A.
Proof. by rewrite conjmxE mxrank_map. Qed.

Lemma adjmx_const m n a : (const_mx a : 'M[R]_(m,n))^*t = (const_mx a^*).
Proof. by apply/matrixP=>i j; rewrite !mxE. Qed.

Lemma conjmx_const m n a : (const_mx a : 'M[R]_(m,n))^*m = (const_mx a^*).
Proof. by apply/matrixP=>i j; rewrite !mxE. Qed.

Lemma adjmx_tens m n p q (M :'M[R]_(m,n)) (N : 'M_(p,q)) :
  (M *t N)^*t = M^*t *t N^*t.
Proof. by rewrite !adjmxE trmx_tens map_mxT. Qed.

Lemma conjmx_tens m n p q (M :'M[R]_(m,n)) (N : 'M_(p,q)) :
  (M *t N)^*m = M^*m *t N^*m.
Proof. by rewrite conjmxE map_mxT. Qed.

End ConjAdjmxTheory.

(* 1 * 1 <-> 1 is convertable, but might cause 
  difficulty when use it for dependent variables *)
Section tens_coerce.
Variable (R : ringType).

Lemma tensrvrvE m n (A : 'rV[R]_m) (B : 'rV[R]_n) :
  A *t B = castmx (mul1n 1, erefl) (A *t B) :> 'M_(1,_).
Proof. by rewrite castmx_id. Qed.

Lemma tenscvcvE m n (A : 'cV[R]_m) (B : 'cV[R]_n) :
  A *t B = castmx (erefl, mul1n 1) (A *t B) :> 'M_(_,1).
Proof. by rewrite castmx_id. Qed.

Definition tensvE := (tensrvrvE, tenscvcvE).

Lemma diag_mx_tens m n (A : 'rV[R]_m) (B : 'rV[R]_n) :
  diag_mx (A *t B) = diag_mx A *t diag_mx B.
Proof.
apply/matrixP=>i j; rewrite !mxE.
case: (mxtens_indexP i)=>i0 i1; case: (mxtens_indexP j)=>j0 j1.
rewrite -(can_eq (@mxtens_unindexK _ _)) !mxtens_indexK/= !ord1 {1}/eq_op/=.
by case: eqP=>/= _; case: eqP=>/= _; rewrite ?mulr0n ?mulr1n// ?mulr0// mul0r.
Qed.

End tens_coerce.

Lemma mxtrace_tens (C : ringType) m n (M :'M[C]_m) (N : 'M_n) :
  \tr (M *t N) = \tr M * \tr N.
Proof.
rewrite /mxtrace mulr_suml; symmetry.
under eq_bigr do rewrite mulr_sumr.
under [RHS]eq_bigr do rewrite mxE.
rewrite pair_big; apply: reindex=>//=.
by exists (@mxtens_index _ _)=> k; rewrite (mxtens_indexK, mxtens_unindexK).
Qed.

Section mxtens_index_big.

Variable (R : Type) (idx : R).

Section reindex.
Variable (op : SemiGroup.com_law R).

Lemma reindex_mxtens_index [m n] [P : pred 'I_(m * n)] (F : 'I_(m * n) -> R) :
\big[op/idx]_(i | P i) F i = \big[op/idx]_(j | P (mxtens_index j)) F (mxtens_index j).
Proof.
apply/reindex; exists (@mxtens_unindex _ _)=>i _;
by rewrite ?mxtens_indexK// mxtens_unindexK.
Qed.

Lemma reindex_mxtens_unindex [m n] [P : pred ('I_m * 'I_n)] (F : ('I_m * 'I_n) -> R) :
\big[op/idx]_(i | P i) F i = \big[op/idx]_(j | P (mxtens_unindex j)) F (mxtens_unindex j).
Proof.
apply/reindex; exists (@mxtens_index _ _)=>i _;
by rewrite ?mxtens_indexK// mxtens_unindexK.
Qed.

End reindex.

Lemma mxtens_index_pairV (op : Monoid.com_law idx) m n (f : 'I_(m*n) -> R) :
  \big[op/idx]_i f i = \big[op/idx]_i \big[op/idx]_j f (mxtens_index (i,j)).
Proof.
rewrite pair_big; apply: reindex=> //=.
exists (@mxtens_unindex _ _)=> i;
rewrite (mxtens_indexK, mxtens_unindexK)// => _.
by rewrite -surjective_pairing.
Qed.

Local Notation "0" := idx.
Variable times : Monoid.mul_law 0.
Local Notation "*%M" := times (at level 0).
Local Notation "x * y" := (times x y).
Variable plus : Monoid.add_law 0 *%M.
Local Notation "+%M" := plus (at level 0).
Local Notation "x + y" := (plus x y).

Lemma mxtens_index_distr m n (Fm : 'I_m -> R) (Fn : 'I_n -> R) :
  (\big[+%M/0]_(i < m) Fm i) * (\big[+%M/0]_(i < n) Fn i)
  = \big[+%M/0]_(i < m * n) ((Fm (mxtens_unindex i).1) * (Fn (mxtens_unindex i).2)).
Proof.
rewrite big_distrlr pair_big; apply: reindex=> //=.
by exists (@mxtens_index _ _)=> i; rewrite (mxtens_indexK, mxtens_unindexK).
Qed.

End mxtens_index_big.

Arguments reindex_mxtens_index [R idx op m n P] F.
Arguments reindex_mxtens_unindex [R idx op m n P] F.
Arguments mxtens_index_pairV [R idx op m n] f.
Arguments mxtens_index_distr [R idx times plus m n] Fm Fn.

Section mxtens_swap.
Variable (R : ringType).

Lemma tr_tens m n (A : 'M[R]_(m * n, m * n)) :
  \tr A = \sum_i\sum_j A (mxtens_index (i, j)) (mxtens_index (i, j)).
Proof. by rewrite /mxtrace mxtens_index_pairV. Qed.

Lemma matrix_tenP m n p q (A B : 'M[R]_(m * p, n * q)) :
  (forall i j k l, A (mxtens_index (i, j)) (mxtens_index (k, l)) 
    = B (mxtens_index (i, j)) (mxtens_index (k, l))) -> A = B.
Proof.
move=>P; apply/matrixP=>i j.
case: (mxtens_indexP i)=> i0 i1; case: (mxtens_indexP j)=> j0 j1.
by rewrite P.
Qed.

Definition mxswap m n p q (A : 'M[R]_(m * p, n * q)) : 'M[R]_(p * m, q * n) :=
  \matrix_(i,j) A (mxtens_index ((mxtens_unindex i).2,(mxtens_unindex i).1))
  (mxtens_index ((mxtens_unindex j).2,(mxtens_unindex j).1)).

Lemma mxswapK m n p q : cancel (@mxswap m n p q) (@mxswap p q m n).
Proof.
by move=>x; apply/matrixP=>i j; rewrite !mxE !mxtens_indexK/= !mxtens_unindexK.
Qed.

Lemma mxswap_is_linear m n p q : linear (@mxswap m n p q).
Proof. by move=>a x y; apply/matrixP=>i j; rewrite !mxE. Qed.

HB.instance Definition _ m n p q := GRing.isLinear.Build R 
  'M[R]_(m * p, n * q) 'M[R]_(p * m, q * n) *:%R (@mxswap m n p q)
  (@mxswap_is_linear m n p q).

Lemma mxswap_inj m n p q : injective (@mxswap m n p q).
Proof. exact: (can_inj (@mxswapK _ _ _ _)). Qed.

Lemma mxswap_trace m p (A : 'M_(m * p)) :
  \tr (mxswap A) = \tr A.
Proof.
rewrite !tr_tens exchange_big; apply eq_bigr=>i _; apply eq_bigr=>j _.
by rewrite mxE !mxtens_indexK/=.
Qed.

Lemma mxswap_mul m n p q r s (A : 'M_(m * p, n * q)) (B : 'M_(n * q, r * s)) :
  mxswap A *m mxswap B = mxswap (A *m B).
Proof.
apply/matrix_tenP=>i j k l.
rewrite !mxE mxtens_index_pairV exchange_big [RHS]mxtens_index_pairV.
apply eq_bigr=>a _; apply eq_bigr=>b _.
by rewrite !mxE !mxtens_indexK/=.
Qed.

Lemma mxswap_tr m n p q (A : 'M_(m * p, n * q)) :
  ((mxswap A)^T = mxswap (A ^T))%R.
Proof. by apply/matrix_tenP=>i j k l; rewrite !mxE. Qed.

Lemma mxswap_map (f : {rmorphism R -> R}) m n p q (A : 'M_(m * p, n * q)) :
  map_mx f (mxswap A) = mxswap (map_mx f A).
Proof. by apply/matrix_tenP=>i j k l; rewrite !mxE. Qed.

Definition perm_swap_fun (m n : nat) (i : 'I_(m * n)) :=
  cast_ord (mulnC _ _) (mxtens_index ((mxtens_unindex i).2, (mxtens_unindex i).1)).

Lemma mxtens_index_inj m n : injective (@mxtens_index m n).
Proof. by apply/(can_inj (@mxtens_indexK m n)). Qed.
Lemma mxtens_unindex_inj m n : injective (@mxtens_unindex m n).
Proof. by apply/(can_inj (@mxtens_unindexK m n)). Qed.

Lemma perm_swap_fun_inj m n : injective (@perm_swap_fun m n).
Proof.
move=>i j /cast_ord_inj /mxtens_index_inj [] P1 P2.
apply/mxtens_unindex_inj/eqP; rewrite -pair_eqE.
by apply/andP; split; apply/eqP/val_inj=>/=.
Qed.

Definition perm_swap {m n} : {perm 'I_(m * n)} := perm (@perm_swap_fun_inj m n).

Lemma mxswap_permE m n p q (A : 'M_(m * p, n * q)) :
  mxswap A = (row_perm perm_swap (col_perm perm_swap (castmx (mulnC _ _, mulnC _ _) A))).
Proof.
apply/matrix_tenP=>i j k l.
by rewrite !mxE castmxE !permE /perm_swap_fun !cast_ord_comp !cast_ord_id.
Qed.

(* partial trace *)
Lemma mxtens_index1 m (i : 'I_m) : (cast_ord (esym (muln1 m)) i) = mxtens_index (i,ord0).
Proof. by apply/val_inj=>/=; rewrite muln1 addn0. Qed.
Lemma mxtens_1index m (i : 'I_m) : (cast_ord (esym (mul1n m)) i) = mxtens_index (ord0,i).
Proof. by apply/val_inj=>/=; rewrite mul0n. Qed.

Lemma tens_mx_cast1l m n (M : 'M[R]_(m,n)) :
  1%:M *t M  = castmx (esym (mul1n _), esym (mul1n _)) M.
Proof.
apply/matrixP=> i j.
case: (mxtens_indexP i)=> i0 i1; case: (mxtens_indexP j)=> j0 j1.
rewrite tensmxE [i0]ord1 [j0]ord1 !castmxE !mxE /= mul1r.
by f_equal; apply: val_inj=> /=; rewrite mul0n add0n.
Qed.

Lemma tens_mx_cast1r m n (M : 'M[R]_(m,n)) :
  M *t 1%:M  = castmx (esym (muln1 _), esym (muln1 _)) M.
Proof.
apply/matrixP=> i j.
case: (mxtens_indexP i)=> i0 i1; case: (mxtens_indexP j)=> j0 j1.
rewrite tensmxE !ord1 !castmxE !mxE /= mulr1;
by f_equal; apply: val_inj=> /=; rewrite muln1 addn0.
Qed.

Lemma tens_mx_cast1lE m n (M : 'M[R]_(m,n)) :
  M = castmx (mul1n _, mul1n _) (1%:M *t M).
Proof. by rewrite tens_mx_cast1l castmx_comp !etrans_esymV. Qed.

Lemma tens_mx_cast1rE m n (M : 'M[R]_(m,n)) :
  M  = castmx (muln1 _, muln1 _) (M *t 1%:M).
Proof. by rewrite tens_mx_cast1r castmx_comp !etrans_esymV. Qed.

Definition ptrace2 m n (A : 'M[R]_(m * n)) :=
  castmx (muln1 _ , muln1 _)
  (\sum_i (1%:M *t delta_mx (0:'I_1) i) *m A *m (1%:M *t delta_mx i (0:'I_1))).

Definition ptrace1 m n (A : 'M[R]_(m * n)) :=
  castmx (mul1n _ , mul1n _)
  (\sum_i (delta_mx (0:'I_1) i *t 1%:M) *m A *m (delta_mx i (0:'I_1) *t 1%:M)).

Lemma tensmxE_mid m n p q (A : 'M[R]_(m,p*q)) (B: 'M_(p*q,n)) i j :
  (A *m B) i j = \sum_i1 \sum_i2 A i (mxtens_index (i1,i2)) * B (mxtens_index (i1,i2)) j.
Proof.
by rewrite mxE pair_big; apply/reindex; exists (@mxtens_unindex _ _)=> k; 
rewrite (mxtens_indexK, mxtens_unindexK) -?surjective_pairing.
Qed.

Lemma tens_delta_mx1_mulEl m n s t (A : 'M[R]_(m * n, s)) (i : 'I_t) j k p q :
  (delta_mx i j *t 1%:M *m A) (mxtens_index (k, p)) q
    = (i == k)%:R * A (mxtens_index (j, p)) q.
Proof.
rewrite mxE (bigD1 (mxtens_index (j, p)))//= big1/=.
move=>x; case: (mxtens_indexP x)=>i1 i2.
  by rewrite (can_eq (@mxtens_indexK _ _))/eq_op/= negb_and tensmxE 
    !mxE [p == i2]eq_sym=>/orP[]/negPf->; rewrite ?andbF ?(mul0r, mulr0).
by rewrite tensmxE mxE mxE !eqxx eq_sym andbT mulr1 addr0.
Qed.

Lemma tens_delta_mx1_mulEr m n s t (A : 'M[R]_(s, m * n)) i (j : 'I_t) k p q :
  (A *m (delta_mx i j *t 1%:M)) p (mxtens_index (k, q))
    = (j == k)%:R * A p (mxtens_index (i, q)).
Proof.
rewrite mxE (bigD1 (mxtens_index (i, q)))//= big1/=.
move=>x; case: (mxtens_indexP x)=>i1 i2.
  by rewrite (can_eq (@mxtens_indexK _ _))/eq_op/= negb_and tensmxE
    !mxE=>/orP[]/negPf->; rewrite ?andbF ?(mul0r, mulr0).
rewrite tensmxE mxE mxE !eqxx eq_sym addr0/= mulr1.
by case: eqP=> _; rewrite ?mulr1 ?mul1r ?mul0r ?mulr0.
Qed.

Lemma tensmx11 m n : 
  (1%:M : 'M[R]_m) *t (1%:M : 'M[R]_n) = 1%:M.
Proof.   
apply/matrixP=>i j; case: (mxtens_indexP i)=>i1 i2; case: (mxtens_indexP j)=>j1 j2.
rewrite mxE !mxtens_indexK/= !mxE (can_eq (@mxtens_indexK _ _)) -pair_eqE/=;
by do ! case: eqP; rewrite ?mulr0 ?mulr1.
Qed.

End mxtens_swap.

Lemma mxswap_adj (R: numClosedFieldType) m n p q (A : 'M[R]_(m * p, n * q)) :
  (mxswap A)^*t = mxswap (A ^*t).
Proof. by apply/matrix_tenP=>i j k l; rewrite !mxE. Qed.

Lemma mxswap_conj (R: numClosedFieldType) m n p q (A : 'M[R]_(m * p, n * q)) :
  (mxswap A)^*m = mxswap (A ^*m).
Proof. by apply/matrix_tenP=>i j k l; rewrite !mxE. Qed.

Section MxtensPTrace.
Variable (R : comRingType).
Local Open Scope lfun_scope.

Lemma mxswap_tens m n p q (A : 'M[R]_(m,n)) (B : 'M[R]_(p,q)) :
  mxswap (A *t B) = B *t A.
Proof.
by apply/matrix_tenP=>i j s t; rewrite mxE !tensmxE !mxtens_indexK/= mulrC.
Qed.

Lemma ptrace2E1 m n (A : 'M[R]_(m * n)) :
  ptrace2 A = ptrace1 (mxswap A).
Proof.
symmetry; rewrite/ptrace1/ptrace2 !linear_sum/=; apply eq_bigr=>i _.
rewrite -mxswap_tens mxswap_mul -[X in _ *m X]mxswap_tens mxswap_mul.
by apply/matrixP=>a b; rewrite !castmxE/= !mxtens_index1 !mxtens_1index mxE !mxtens_indexK.
Qed.
Lemma ptrace1E2 m n (A : 'M[R]_(m * n)) :
  ptrace1 A = ptrace2 (mxswap A).
Proof. by rewrite ptrace2E1 mxswapK. Qed.

Lemma ptrace2_is_linear m n : linear (@ptrace2 R m n).
Proof.
move=>c A B; rewrite /ptrace2 -linearP/= scaler_sumr -big_split/=; f_equal.
apply eq_bigr=>i _; rewrite mulmxDr mulmxDl. 
congr (_ + _); by rewrite scalemxAl scalemxAr.
Qed.

HB.instance Definition _ m n := GRing.isLinear.Build R 'M[R]_(m * n) 'M[R]_m
  *:%R (@ptrace2 R m n) (@ptrace2_is_linear m n).

Lemma ptrace1_is_linear m n : linear (@ptrace1 R m n).
Proof. by move=>c A B; rewrite ptrace1E2 linearP/= linearP/= -!ptrace1E2. Qed.

HB.instance Definition _ m n := GRing.isLinear.Build R 'M[R]_(m * n) 'M[R]_n
  *:%R (@ptrace1 R m n) (@ptrace1_is_linear m n).

Lemma tr_ptrace2 m n (A: 'M[R]_(m*n)) : \tr A = \tr (ptrace2 A).
Proof.
rewrite !tr_tens/=; apply eq_bigr=>i _.
rewrite /ptrace2/= linear_sum/= summxE; apply eq_bigr=>j _.
rewrite castmxE/= !mxtens_index1 mxE (bigD1 (mxtens_index (i, j)))//= big1; last first.
rewrite !tensmxE mxE (bigD1 (mxtens_index (i, j)))//= big1; last first.
by rewrite tensmxE !mxE !eqxx/= !addr0 ?(mul1r, mulr1).
all: move=>k; case: (mxtens_indexP k)=> i0 i1;
rewrite (inj_eq (can_inj (@mxtens_indexK _ _))) -pair_eqE/= negb_and=>
/orP[/negPf P|/negPf P]; rewrite tensmxE !mxE ?P/= 1 ? eq_sym ?P ?(mul0r,mulr0)//.
Qed.

Lemma tr_ptrace1 m n (A: 'M[R]_(m*n)) : \tr A = \tr (ptrace1 A).
Proof. by rewrite ptrace1E2 -tr_ptrace2 mxswap_trace. Qed.

Lemma ptrace1_mulmxI m n (A: 'M[R]_(m*n)) B : 
  ptrace1 (A *m (1%:M *t B)) = ptrace1 A *m B.
Proof.
rewrite/ptrace1 {2}[B]tens_mx_cast1lE castmx_mul; f_equal.
rewrite linear_suml; apply eq_bigr => i _.
by rewrite/= -!mulmxA !tensmx_mul !mulmx1 !mul1mx.
Qed.

Lemma ptrace1_mulImx m n (A: 'M[R]_(m*n)) B : 
  ptrace1 ((1%:M *t B) *m A) = B *m ptrace1 A.
Proof.
rewrite/ptrace1 {2}[B]tens_mx_cast1lE castmx_mul; f_equal.
rewrite linear_sumr; apply eq_bigr => i _.
by rewrite/= !mulmxA !tensmx_mul !mulmx1 !mul1mx.
Qed.

Lemma ptrace2_mulmxI m n (A: 'M[R]_(m*n)) B : 
  ptrace2 (A *m (B *t 1%:M)) = ptrace2 A *m B.
Proof. by rewrite ptrace2E1 -mxswap_mul mxswap_tens ptrace1_mulmxI -ptrace2E1. Qed.

Lemma ptrace2_mulImx m n (A: 'M[R]_(m*n)) B : 
  ptrace2 ((B *t 1%:M) *m A) = B *m ptrace2 A.
Proof. by rewrite ptrace2E1 -mxswap_mul mxswap_tens ptrace1_mulImx -ptrace2E1. Qed.

End MxtensPTrace.

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

Section PredMxTens.
Variable (R : numDomainType) (m n p q : nat).
Implicit Type (A : 'M[R]_(m,n)) (B : 'M[R]_(p,q)).

Lemma realmx_tens A B : 
  A \is a realmx -> B \is a realmx -> A *t B \is a realmx.
Proof.
move=>/realmxP PA /realmxP PB.
apply/realmxP=>i j.
case: (mxtens_indexP i)=>i0 i1; case: (mxtens_indexP j)=>j0 j1.
by rewrite tensmxE realM.
Qed.

Lemma posmx_tens A B : 
  A \is a posmx -> B \is a posmx -> A *t B \is a posmx.
Proof.
move=>/posmxP PA /posmxP PB.
apply/posmxP=>i j.
case: (mxtens_indexP i)=>i0 i1; case: (mxtens_indexP j)=>j0 j1.
by rewrite tensmxE posrE mulr_gt0// -posrE.
Qed.

Lemma nnegmx_tens A B : 
  A \is a nnegmx -> B \is a nnegmx -> A *t B \is a nnegmx.
Proof.
move=>/nnegmxP PA /nnegmxP PB.
apply/nnegmxP=>i j.
case: (mxtens_indexP i)=>i0 i1; case: (mxtens_indexP j)=>j0 j1.
by rewrite tensmxE nnegrE mulr_ge0// -nnegrE.
Qed.

Lemma uintmx_tens A B : 
  A \is a uintmx -> B \is a uintmx -> A *t B \is a uintmx.
Proof.
move=>/uintmxP PA /uintmxP PB.
apply/uintmxP=>i j.
case: (mxtens_indexP i)=>i0 i1; case: (mxtens_indexP j)=>j0 j1.
rewrite tensmxE mulr_ge0/= ?mulr_ile1//;
by move: (PA i0 j0) (PB i1 j1)=>/andP[] + + /andP[].
Qed.

Lemma boolmx_tens A B : 
  A \is a boolmx -> B \is a boolmx -> A *t B \is a boolmx.
Proof.
move=>/boolmxP PA /boolmxP PB.
apply/boolmxP=>i j.
case: (mxtens_indexP i)=>i0 i1; case: (mxtens_indexP j)=>j0 j1.
rewrite tensmxE; move: (PA i0 j0)=>/orP[/eqP->|/eqP->];
by rewrite ?mul1r// mul0r eqxx.
Qed.

End PredMxTens.

Section rank_extra.
Variable (C : numClosedFieldType).

(* normalmx unitarymx unitmx already exists *)
Lemma unitarymxPV m (A : 'M[C]_m) : 
  reflect (A ^*t *m A = 1%:M) (A \is unitarymx).
Proof. rewrite -{2}(adjmxK A) adjmxE -trmxC_unitary; apply: unitarymxP. Qed.

Lemma trmx_unitaryP m (U : 'M[C]_m) :
  U \is unitarymx -> U^T \is unitarymx.
Proof. by rewrite trmx_unitary. Qed.

Lemma conjmx_unitary m n (U : 'M[C]_(m,n)) :
  U^*m \is unitarymx = (U \is unitarymx).
Proof. by rewrite conjC_unitary. Qed.

Lemma conjmx_unitaryP m n (U : 'M[C]_(m,n)) :
  U \is unitarymx -> U^*m \is unitarymx.
Proof. by rewrite conjmx_unitary. Qed.

Lemma adjmx_unitary m (U : 'M[C]_m) :
  U^*t \is unitarymx = (U \is unitarymx).
Proof. by rewrite adjmxE trmxC_unitary. Qed.

Lemma adjmx_unitaryP m (U : 'M[C]_m) :
  U \is unitarymx -> U^*t \is unitarymx.
Proof. by rewrite adjmx_unitary. Qed.

Lemma mulUmx m n (U : 'M[C]_m) (A B : 'M[C]_(m,n)) : 
  U \is unitarymx -> U *m A = B <-> A = U ^*t *m B.
Proof.
move=>P; move: P {+}P=>/unitarymxP P1 /unitarymxPV P2.
by split=>[ <-|->]; rewrite mulmxA ?P1 ?P2 mul1mx.
Qed.

Lemma mulUCmx m n (U : 'M[C]_m) (A B : 'M[C]_(m,n)) : 
  U \is unitarymx -> U ^*t *m A = B <-> A = U *m B.
Proof. 
move=>P; move: P {+}P=>/unitarymxP P1 /unitarymxPV P2.
by split=>[ <-|->]; rewrite mulmxA ?P1 ?P2 mul1mx.
Qed.

Lemma mulmxU m n (U : 'M[C]_n) (A B : 'M[C]_(m,n)) :
  U \is unitarymx -> A *m U = B <-> A = B *m U ^*t.
Proof.
move=>P; move: P {+}P=>/unitarymxP P1 /unitarymxPV P2.
by split=>[ <-|->]; rewrite -mulmxA ?P1 ?P2 mulmx1.
Qed.

Lemma mulmxUC m n (U : 'M[C]_n) (A B : 'M[C]_(m,n)) :
  U \is unitarymx -> A *m U ^*t = B <-> A = B *m U.
Proof.
move=>P; move: P {+}P=>/unitarymxP P1 /unitarymxPV P2.
by split=>[ <-|->]; rewrite -mulmxA ?P1 ?P2 mulmx1.
Qed.

Lemma unitarymxK m n  (U : 'M[C]_(m,n)) : U \is unitarymx -> U *m U ^*t = 1%:M.
Proof. by move/unitarymxP. Qed.

Lemma unitarymxKV m  (U : 'M[C]_m) : U \is unitarymx -> U ^*t *m U = 1%:M.
Proof. by move/unitarymxPV. Qed.

Lemma row_unitarymx m n (M : 'M[C]_(m, n)) i :
  M \is unitarymx -> row i M \is unitarymx.
Proof.
move=>/row_unitarymxP/(_ i i) Pi; apply/row_unitarymxP=>j k.
by rewrite !ord1 !row_idem Pi !eqxx.
Qed.

Lemma mxrank_mulmxU m n r (A : 'M[C]_(m,n)) (U : 'M[C]_(n,r)) :
  U \is unitarymx -> \rank (A *m U) = \rank A.
Proof. by move=>/mxrank_unitary P1; rewrite mxrankMfree// /row_free P1. Qed.

Lemma mxrank_mulUmx m n (U : 'M[C]_m) (A : 'M[C]_(m,n)) :
  U \is unitarymx -> \rank (U *m A) = \rank A.
Proof.
by move=>P; rewrite -mxrank_tr trmx_mul mxrank_mulmxU ?trmx_unitary// mxrank_tr.
Qed.

Lemma mxrank_mulmxUC m n (A : 'M[C]_(m,n)) (U : 'M[C]_n) :
  U \is unitarymx -> \rank (A *m U^*t) = \rank A.
Proof. by move=>P; rewrite mxrank_mulmxU// trmxC_unitary. Qed.

Lemma mxrank_mulUCmx m n r (U : 'M[C]_(m,r)) (A : 'M[C]_(m,n)) :
  U \is unitarymx -> \rank (U^*t *m A) = \rank A.
Proof.
by move=>PU; rewrite -mxrank_tr -mxrank_conj -adjmxTC 
  adjmxM adjmxK mxrank_mulmxU// mxrank_adj.
Qed.

Lemma dotmx_row_mx m n (u v : 'rV[C]_m) (w t : 'rV[C]_n) :
  dotmx (row_mx u w) (row_mx v t) = dotmx u v + dotmx w t.
Proof.
rewrite !dotmxE !mxE/= big_split_ord/=; f_equal; apply eq_bigr=>i _;
by rewrite ?row_mxEl ?row_mxEr mxE tr_row_mx ?col_mxEu ?col_mxEd !mxE.
Qed.

Lemma row_mx0_unitarymx m n r (U : 'M[C]_(m,n)) :
  U \is unitarymx -> row_mx U (0 : 'M_(m,r)) \is unitarymx.
Proof.
move=>/row_unitarymxP PU; apply/row_unitarymxP=>i j.
by rewrite !row_row_mx !dotmx_row_mx row0 linear0l addr0.
Qed.

Lemma row_0mx_unitarymx m n r (U : 'M[C]_(m,n)) :
  U \is unitarymx -> row_mx (0 : 'M_(m,r)) U \is unitarymx.
Proof.
move=>/row_unitarymxP PU; apply/row_unitarymxP=>i j.
by rewrite !row_row_mx !dotmx_row_mx row0 linear0l add0r.
Qed.

Lemma mxdiag_unitary m n p q (U : 'M[C]_(m,n)) (V : 'M[C]_(p,q)) :
  U \is unitarymx -> V \is unitarymx -> block_mx U 0 0 V \is unitarymx.
Proof.
move=>/row_unitarymxP PU /row_unitarymxP PV.
apply/row_unitarymxP=>i j.
case: (split_ordP i)=>i1 ->; case: (split_ordP j)=>j1 ->;
by rewrite /block_mx ?rowKu ?rowKd !row_row_mx !dotmx_row_mx ?row0 
  ?linear0l ?linear0r ?addr0 ?add0r ?eq_lrshift// ?eq_rlshift// ?eq_rshift//.
Qed.

End rank_extra.

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

#[global] Hint Extern 0 (is_true (spectralmx _ \is unitarymx)) => 
  (apply/spectral_unitarymx) : core.
#[global] Hint Extern 0 (is_true ((spectralmx _)^*t \is unitarymx)) => 
  (apply/adjmx_unitaryP/spectral_unitarymx) : core.
#[global] Hint Extern 0 (is_true ((spectralmx _)^*m \is unitarymx)) => 
  (apply/conjmx_unitaryP/spectral_unitarymx) : core.
#[global] Hint Extern 0 (is_true ((spectralmx _)^T \is unitarymx)) => 
  (apply/trmx_unitaryP/spectral_unitarymx) : core.
#[global] Hint Extern 0 (is_true (eigenmx _ \is unitarymx)) => 
  (apply/eigen_unitarymx) : core.
#[global] Hint Extern 0 (is_true ((eigenmx _)^*t \is unitarymx)) => 
  (apply/adjmx_unitaryP/eigen_unitarymx) : core.
#[global] Hint Extern 0 (is_true ((eigenmx _)^*m \is unitarymx)) => 
  (apply/conjmx_unitaryP/eigen_unitarymx) : core.
#[global] Hint Extern 0 (is_true ((eigenmx _)^T \is unitarymx)) => 
  (apply/trmx_unitaryP/eigen_unitarymx) : core.

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
1,2: by apply/eqP; rewrite ?mxrank_tr; apply mxrank_unitary.
by rewrite mxrank_tr.
Qed.

Lemma rank11 (N : 'M[R]_1) : \rank N = (N 0 0 != 0).
Proof.
rewrite rank_rV; case: eqP=>[->|]; case: eqP=>//. by rewrite mxE.
move=>P1 P2; exfalso; apply P2; apply/matrixP=>i j; by rewrite !mxE !ord1.
Qed.

Lemma rank_diag_mx n (N: 'rV[R]_n) :
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
rewrite rank_diag_mx=>/sum_nat_eq1[i P]; exists i.
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

Lemma projmx_tr M : 
  M \is projmx -> \tr M = (\rank M)%:R.
Proof.
move=>/projmxP[/hermmx_normal/eigen_dec P1 /boolmxP P2].
rewrite P1 mxtrace_mulC mulmxA unitarymxKV// mul1mx mxrank_mulmxUC// mxrank_mulUmx//.
rewrite rank_diag_mx mxtrace_diag natr_sum; apply eq_bigr=>i _.
by move: (P2 ord0 i)=>/orP[/eqP->|/eqP->]; rewrite ?oner_neq0// eqxx.
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

Lemma formV_psd p q (M : 'M[R]_(p,q)) : (M ^*t *m M) \is psdmx.
Proof.
apply/psdmx_dot=>v; rewrite mulmxA -adjmxM -mulmxA nnegrE trace_mx11 mxE.
by apply sumr_ge0=>/= i _; rewrite mxE mxE -normCKC exprn_ge0.
Qed.

Lemma form_psd p q (M : 'M[R]_(p,q)) : (M *m M ^*t) \is psdmx.
Proof. by rewrite -{1}(adjmxK M) formV_psd. Qed.

Lemma psdmx1 n : (1%:M : 'M[R]_n) \is psdmx.
Proof. by rewrite -[1%:M]mulmx1 -{1}adjmx1 formV_psd. Qed.

Lemma obsmx0 n : (0 : 'M[R]_n) \is obsmx.
Proof. by rewrite obsmx_psd_eq psdmx0 subr0 psdmx1. Qed.

Lemma obsmx1 n : (1%:M : 'M[R]_n) \is obsmx.
Proof. by rewrite obsmx_psd_eq subrr psdmx0 psdmx1. Qed.

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

Lemma psdmxD: operator_closed (@psdmx R m) (+%R).
Proof. 
move=> A B /psdmx_dot hA /psdmx_dot hB. apply/psdmx_dot=>u.
move: (hA u) (hB u). rewrite mulmxDr mulmxDl linearD/= !nnegrE.
by apply ler_wpDl.
Qed.

Lemma psdmx_sum I r (P : pred I) (F: I -> 'M[R]_m) :
  (forall i, P i -> F i \is psdmx) -> \sum_(i <- r | P i) F i \is psdmx.
Proof. 
elim/big_ind: _=>[_||i Pi /(_ _ Pi)//]; first by apply psdmx0.
by move=>x y ++ Pi; move=>/(_ Pi) Px /(_ Pi) Py; apply/psdmxD.
Qed.

Fact psdmx_addr_closed : addr_closed (@psdmx R m).
Proof. split. apply psdmx0. apply psdmxD. Qed.

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

Lemma distvC v w : `[ v - w ] = `[ w - v ].
Proof. by rewrite -opprB normvN. Qed.

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

Lemma normv_sum I (r : seq I) (P: pred I) (f : I -> V) :
  `[ \sum_(i <- r | P i) f i ] <= \sum_(i <- r | P i) `[ f i ].
Proof.
elim: r => [|x r IH]; first by rewrite !big_nil normv0.
rewrite !big_cons. case: (P x)=>//.
apply (le_trans (lev_normD _ _)). by apply lerD.
Qed.

Lemma normv_id v : `| `[v] | = `[v].
Proof. by rewrite ger0_norm// normv_ge0. Qed.

Lemma normv_le0 v : `[v] <= 0 = (v == 0).
Proof. by rewrite -normv_eq0 eq_le normv_ge0 andbT. Qed.

Lemma normv_lt0 v : `[v] < 0 = false.
Proof. by rewrite lt_neqAle normv_le0 normv_eq0 andNb. Qed.

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
  lev_add2rP : forall (z x y : T), x <= y -> (x + z) <= (y + z);
  lev_pscale2lP : forall (e : R) (x y : T), 0 < e -> x <= y -> (e *: x) <= (e *: y);
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
  pscalev_lge0 : forall (x : T) (e : R), 0 < x -> 0 <= (e *: x) = (0 <= e);
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

Lemma subv_ge0 x y : ('0 <= x - y) = (y <= x).
Proof. 
apply/Bool.eq_iff_eq_true; split=>[/(@lev_add2rP R T y)|/(@lev_add2rP R T(-y))];
by rewrite ?addrNK ?add0r// addrN.
Qed.

Lemma subv_gt0 x y : ('0 < y - x) = (x < y).
Proof. by rewrite !lt_def subr_eq0 subv_ge0. Qed.
Lemma subv_le0  x y : (y - x <= 0) = (y <= x).
Proof. by rewrite -[LHS]subv_ge0 opprB add0r subv_ge0. Qed.
Lemma subv_lt0  x y : (y - x < 0) = (y < x).
Proof. by rewrite -[LHS]subv_gt0 opprB add0r subv_gt0. Qed.

Definition subv_lte0 := (subv_le0, subv_lt0).
Definition subv_gte0 := (subv_ge0, subv_gt0).
Definition subv_cp0 := (subv_lte0, subv_gte0).

Lemma levN2 : {mono (-%R : T -> T) : x y /~ x <= y }.
Proof. by move=>x y; rewrite -subv_ge0 opprK addrC subv_ge0. Qed.
Hint Resolve levN2 : core.

Lemma ltvN2 : {mono (-%R : T -> T) : x y /~ x < y }.
Proof. by move=> x y /=; rewrite leW_nmono. Qed.
Hint Resolve ltvN2 : core.
Definition ltev_opp2 := (levN2, ltvN2).

Lemma addv_ge0 x y : '0 <= x -> '0 <= y -> '0 <= x + y.
Proof.
by move=>P1 P2; apply: (le_trans P1); rewrite -subv_ge0 addrC addrA addNr add0r.
Qed.

Lemma addv_gt0 x y : '0 < x -> '0 < y -> '0 < x + y.
Proof.
rewrite !lt_def=>/andP[/negPf Pf Pf1]/andP[Pg Pg1]; rewrite (addv_ge0 Pf1 Pg1) andbT.
case: eqP=>//= P1; move: Pg1; rewrite -P1 -subv_ge0 opprD addrC addrNK -oppr0 levN2=>P2.
by rewrite -Pf eq_le Pf1 P2.
Qed.

Lemma le0v x : ('0 <= x) = (x == 0) || ('0 < x).
Proof. by rewrite lt_def; case: eqP => // ->; rewrite lexx. Qed.

Lemma levD2r x : {mono +%R^~ x : y z / y <= z}.
Proof. by move=>y z; rewrite -subv_ge0 opprD addrACA addrN addr0 subv_ge0. Qed.

Lemma levNr x y : (x <= - y) = (y <= - x).
Proof. by rewrite (monoRL opprK levN2). Qed.

Lemma ltv_oppr x y : (x < - y) = (y < - x).
Proof. by rewrite (monoRL opprK (leW_nmono levN2)). Qed.

Definition ltev_oppr := (levNr, ltv_oppr).

Lemma levNl x y : (- x <= y) = (- y <= x).
Proof. by rewrite (monoLR opprK levN2). Qed.

Lemma ltvNl x y : (- x < y) = (- y < x).
Proof. by rewrite (monoLR opprK (leW_nmono levN2)). Qed.

Definition ltev_oppl := (levNl, ltvNl).

Lemma oppv_ge0 x : ('0 <= - x) = (x <= 0).
Proof. by rewrite ltev_oppr oppr0. Qed.

Lemma oppv_gt0 x : ('0 < - x) = (x < 0).
Proof. by rewrite ltev_oppr oppr0. Qed.

Definition oppv_gte0 := (oppv_ge0, oppv_gt0).

Lemma oppv_le0 x : (- x <= 0) = ('0 <= x).
Proof. by rewrite ltev_oppl oppr0. Qed.

Lemma oppv_lt0 x : (- x < 0) = ('0 < x).
Proof. by rewrite ltev_oppl oppr0. Qed.

Definition oppv_lte0 := (oppv_le0, oppv_lt0).
Definition oppv_cp0 := (oppv_gte0, oppv_lte0).
Definition ltevNE := (oppv_cp0, ltev_opp2).

Lemma gev0_cp x : '0 <= x -> (- x <= 0) * (- x <= x).
Proof. by move=> hx; rewrite oppv_cp0 hx (@le_trans _ _ '0) ?oppv_cp0. Qed.

Lemma gtv0_cp x : '0 < x ->
  ('0 <= x) * (- x <= 0) * (- x <= x) * (- x < 0) * (- x < x).
Proof.
move=> hx; move: (ltW hx) => hx'; rewrite !gev0_cp hx'=>[//|//|].
by rewrite oppv_cp0 hx (@lt_trans _ _ '0) ?oppv_cp0.
Qed.

Lemma lev0_cp x : x <= 0 -> ('0 <= - x) * (x <= - x).
Proof. by move=> hx; rewrite oppv_cp0 hx (@le_trans _ _ '0) ?oppv_cp0. Qed.

Lemma ltv0_cp x :
  x < 0 -> (x <= 0) * ('0 <= - x) * (x <= - x) * ('0 < - x) * (x < - x).
Proof.
move=> hx; move: (ltW hx) => hx'; rewrite !lev0_cp hx' =>[//|//|].
by rewrite oppv_cp0 hx (@lt_trans _ _ '0) ?oppv_cp0.
Qed.

(* Monotony of addition *)
Lemma levD2l x : {mono +%R x : y z / y <= z}.
Proof. by move=>y z; rewrite ![x + _]addrC levD2r. Qed.

Lemma ltv_add2l x : {mono +%R x : y z / y < z}.
Proof. by move=> y z /=; rewrite (leW_mono (levD2l _)). Qed.

Lemma ltv_add2r x : {mono +%R^~ x : y z / y < z}.
Proof. by move=> y z /=; rewrite (leW_mono (levD2r _)). Qed.

Definition levD2 := (levD2l, levD2r).
Definition ltvD2 := (ltv_add2l, ltv_add2r).
Definition ltev_add2 := (levD2, ltvD2).

(* Addition, subtraction and transitivity *)
Lemma levD x y z t : x <= y -> z <= t -> x + z <= y + t.
Proof. by move=> lxy lzt; rewrite (@le_trans _ _ (y + z)) ?ltev_add2. Qed.

Lemma lev_lt_add x y z t : x <= y -> z < t -> x + z < y + t.
Proof. by move=> lxy lzt; rewrite (@le_lt_trans _ _ (y + z)) ?ltev_add2. Qed.

Lemma ltv_le_add x y z t : x < y -> z <= t -> x + z < y + t.
Proof. by move=> lxy lzt; rewrite (@lt_le_trans _ _ (y + z)) ?ltev_add2. Qed.

Lemma ltvD x y z t : x < y -> z < t -> x + z < y + t.
Proof. by move=> lxy lzt; rewrite ltv_le_add ?ltW. Qed.

Lemma levB x y z t : x <= y -> t <= z -> x - z <= y - t.
Proof. by move=> lxy ltz; rewrite levD ?ltev_opp2. Qed.

Lemma lev_lt_sub x y z t : x <= y -> t < z -> x - z < y - t.
Proof. by move=> lxy lzt; rewrite lev_lt_add ?ltev_opp2. Qed.

Lemma ltv_le_sub x y z t : x < y -> t <= z -> x - z < y - t.
Proof. by move=> lxy lzt; rewrite ltv_le_add ?ltev_opp2. Qed.

Lemma ltv_sub x y z t : x < y -> t < z -> x - z < y - t.
Proof. by move=> lxy lzt; rewrite ltvD ?ltev_opp2. Qed.

Lemma levBlDr x y z : (x - y <= z) = (x <= z + y).
Proof. by rewrite (monoLR (addrK _) (levD2r _)). Qed.

Lemma ltvBlDr x y z : (x - y < z) = (x < z + y).
Proof. by rewrite (monoLR (addrK _) (ltv_add2r _)). Qed.

Lemma levBrDr x y z : (x <= y - z) = (x + z <= y).
Proof. by rewrite (monoLR (addrNK _) (levD2r _)). Qed.

Lemma ltvBrDr x y z : (x < y - z) = (x + z < y).
Proof. by rewrite (monoLR (addrNK _) (ltv_add2r _)). Qed.

Definition lev_sub_addr := (levBlDr, levBrDr).
Definition ltv_sub_addr := (ltvBlDr, ltvBrDr).
Definition ltev_sub_addr := (lev_sub_addr, ltv_sub_addr).

Lemma levBlDl x y z : (x - y <= z) = (x <= y + z).
Proof. by rewrite ltev_sub_addr addrC. Qed.

Lemma ltvBlDl x y z : (x - y < z) = (x < y + z).
Proof. by rewrite ltev_sub_addr addrC. Qed.

Lemma levBrDl x y z : (x <= y - z) = (z + x <= y).
Proof. by rewrite ltev_sub_addr addrC. Qed.

Lemma ltvBrDl x y z : (x < y - z) = (z + x < y).
Proof. by rewrite ltev_sub_addr addrC. Qed.

Definition lev_sub_addl := (levBlDl, levBrDl).
Definition ltv_sub_addl := (ltvBlDl, ltvBrDl).
Definition ltevBDl := (lev_sub_addl, ltv_sub_addl).

Lemma levDl x y : (x <= x + y) = ('0 <= y).
Proof. by rewrite -{1}[x]addr0 ltev_add2. Qed.

Lemma ltvDl x y : (x < x + y) = ('0 < y).
Proof. by rewrite -{1}[x]addr0 ltev_add2. Qed.

Lemma levDr x y : (x <= y + x) = ('0 <= y).
Proof. by rewrite -{1}[x]add0r ltev_add2. Qed.

Lemma ltv_addr x y : (x < y + x) = ('0 < y).
Proof. by rewrite -{1}[x]add0r ltev_add2. Qed.

Lemma gev_addl x y : (x + y <= x) = (y <= 0).
Proof. by rewrite -{2}[x]addr0 ltev_add2. Qed.

Lemma gtv_addl x y : (x + y < x) = (y < 0).
Proof. by rewrite -{2}[x]addr0 ltev_add2. Qed.

Lemma gev_addr x y : (y + x <= x) = (y <= 0).
Proof. by rewrite -{2}[x]add0r ltev_add2. Qed.

Lemma gtv_addr x y : (y + x < x) = (y < 0).
Proof. by rewrite -{2}[x]add0r ltev_add2. Qed.

Definition cpv_add := (levDl, levDr, gev_addl, gev_addl,
                       ltvDl, ltv_addr, gtv_addl, gtv_addl).

(* Addition with levt member knwon to be positive/negative *)
Lemma lev_paddl y x z : '0 <= x -> y <= z -> y <= x + z.
Proof. by move=> *; rewrite -[y]add0r levD. Qed.

Lemma ltv_wpDl y x z : '0 <= x -> y < z -> y < x + z.
Proof. by move=> *; rewrite -[y]add0r lev_lt_add. Qed.

Lemma ltv_spaddl y x z : '0 < x -> y <= z -> y < x + z.
Proof. by move=> *; rewrite -[y]add0r ltv_le_add. Qed.

Lemma ltv_spsaddl y x z : '0 < x -> y < z -> y < x + z.
Proof. by move=> *; rewrite -[y]add0r ltvD. Qed.

Lemma lev_wnDl y x z : x <= 0 -> y <= z -> x + y <= z.
Proof. by move=> *; rewrite -[z]add0r levD. Qed.

Lemma ltv_naddl y x z : x <= 0 -> y < z -> x + y < z.
Proof. by move=> *; rewrite -[z]add0r lev_lt_add. Qed.

Lemma ltv_snaddl y x z : x < 0 -> y <= z -> x + y < z.
Proof. by move=> *; rewrite -[z]add0r ltv_le_add. Qed.

Lemma ltv_snsaddl y x z : x < 0 -> y < z -> x + y < z.
Proof. by move=> *; rewrite -[z]add0r ltvD. Qed.

(* Addition with right member we know positive/negative *)
Lemma lev_wpDr y x z : '0 <= x -> y <= z -> y <= z + x.
Proof. by move=> *; rewrite [_ + x]addrC lev_paddl. Qed.

Lemma ltv_wpDr y x z : '0 <= x -> y < z -> y < z + x.
Proof. by move=> *; rewrite [_ + x]addrC ltv_wpDl. Qed.

Lemma ltv_spaddr y x z : '0 < x -> y <= z -> y < z + x.
Proof. by move=> *; rewrite [_ + x]addrC ltv_spaddl. Qed.

Lemma ltv_spsaddr y x z : '0 < x -> y < z -> y < z + x.
Proof. by move=> *; rewrite [_ + x]addrC ltv_spsaddl. Qed.

Lemma lev_naddr y x z : x <= 0 -> y <= z -> y + x <= z.
Proof. by move=> *; rewrite [_ + x]addrC lev_wnDl. Qed.

Lemma ltv_naddr y x z : x <= 0 -> y < z -> y + x < z.
Proof. by move=> *; rewrite [_ + x]addrC ltv_naddl. Qed.

Lemma ltv_snaddr y x z : x < 0 -> y <= z -> y + x < z.
Proof. by move=> *; rewrite [_ + x]addrC ltv_snaddl. Qed.

Lemma ltv_snsaddr y x z : x < 0 -> y < z -> y + x < z.
Proof. by move=> *; rewrite [_ + x]addrC ltv_snsaddl. Qed.

(* x and y have the same sign and their sum is null *)
Lemma paddv_eq0 x y :
  '0 <= x -> '0 <= y -> (x + y == 0) = (x == 0) && (y == 0).
Proof.
rewrite le0v; case/orP=> [/eqP->|hx]; first by rewrite add0r eqxx.
by rewrite (gt_eqF hx) /= => hy; rewrite gt_eqF ?ltv_spaddl.
Qed.

Lemma naddv_eq0 x y :
  x <= 0 -> y <= 0 -> (x + y == 0) = (x == 0) && (y == 0).
Proof.
by move=> lex0 ley0; rewrite -oppr_eq0 opprD paddv_eq0 ?oppv_cp0 ?oppr_eq0.
Qed.

Lemma addv_ss_eq0 x y :
    ('0 <= x) && ('0 <= y) || (x <= 0) && (y <= 0) ->
  (x + y == 0) = (x == 0) && (y == 0).
Proof. by case/orP=> /andP []; [apply: paddv_eq0 | apply: naddv_eq0]. Qed.

(* big sum and lev *)
Lemma sumv_ge0 I (r : seq I) (P : pred I) (F : I -> T) :
  (forall i, P i -> ('0 <= F i)) -> '0 <= \sum_(i <- r | P i) (F i).
Proof. exact: (@big_ind T _ '0 _ (lexx '0) (@lev_paddl '0)). Qed.  

Lemma lev_sum I (r : seq I) (P : pred I) (F G : I -> T) :
    (forall i, P i -> F i <= G i) ->
  \sum_(i <- r | P i) F i <= \sum_(i <- r | P i) G i.
Proof. exact: (big_ind2 _ (lexx _) levD). Qed.

Lemma lev_sum_nat (m n : nat) (F G : nat -> T) :
  (forall i, (m <= i < n)%N -> F i <= G i) ->
  \sum_(m <= i < n) F i <= \sum_(m <= i < n) G i.
Proof. by move=> le_FG; rewrite !big_nat lev_sum. Qed.

Lemma psumv_eq0 (I : eqType) (r : seq I) (P : pred I) (F : I -> T) :
    (forall i, P i -> '0 <= F i) ->
  (\sum_(i <- r | P i) (F i) == 0) = (all (fun i => (P i) ==> (F i == 0)) r).
Proof.
elim: r=> [|a r ihr hr] /=; rewrite (big_nil, big_cons); first by rewrite eqxx.
by case: ifP=> pa /=; rewrite ?paddv_eq0 ?ihr ?hr ?sumv_ge0.
Qed.

(* :TODO: Cyril : See which form to keep *)
Lemma psumv_eq0P (I : finType) (P : pred I) (F : I -> T) :
     (forall i, P i -> '0 <= F i) -> \sum_(i | P i) F i = 0 ->
  (forall i, P i -> F i = 0).
Proof.
move=> F_ge0 /eqP; rewrite psumv_eq0=>[//|].
rewrite -big_all big_andE => /forallP hF i Pi.
by move: (hF i); rewrite implyTb Pi /= => /eqP.
Qed.

Lemma lt0v x : ('0 < x) = (x != 0) && ('0 <= x). Proof. by rewrite lt_def. Qed.

Lemma lt0v_neq0 x : '0 < x -> x != 0.
Proof. by rewrite lt0v; case/andP. Qed.

Lemma ltv0_neq0 x : x < 0 -> x != 0.
Proof. by rewrite lt_neqAle; case/andP. Qed.

End VOrderTheory.

Section VOrderFieldTheory.
Variable (R: numFieldType) (T : vorderType R).
Implicit Type (x y z : T) (a b c : R).
Local Notation "'0" := (0 : T).

Lemma pscalev_rge0 a y : 0 < a -> ('0 <= a *: y) = ('0 <= y).
Proof.
move=>Pa; apply/Bool.eq_iff_eq_true; split=>P.
have P1 : (a^-1 * a) = 1 by rewrite mulVf// lt0r_neq0.
by rewrite -[y]scale1r -(scaler0 _ a^-1) -P1 -scalerA lev_pscale2lP// invr_gt0.
by rewrite -(scaler0 _ a) lev_pscale2lP.
Qed.

Lemma pscalev_rgt0 a y : 0 < a -> ('0 < a *: y) = ('0 < y).
Proof.
by move=>Pa; move: {+}Pa; rewrite !lt_def 
  scaler_eq0 negb_or pscalev_rge0// =>/andP[->_/=].
Qed.

(* mulr and lev/ltv *)
Lemma lev_pscale2l a : 0 < a -> {mono ( *:%R a : T -> T) : x y / x <= y}.
Proof.
by move=> x_gt0 y z /=; rewrite -subv_ge0 -scalerBr pscalev_rge0// subv_ge0.
Qed.

Lemma ltv_pscale2l a : 0 < a -> {mono ( *:%R a : T -> T) : x y / x < y}.
Proof. by move=> x_gt0; apply: leW_mono (lev_pscale2l _). Qed.

Definition ltev_pscale2l := (lev_pscale2l, ltv_pscale2l).

Lemma lev_nscale2l a : a < 0 -> {mono ( *:%R a : T -> T) : x y /~ x <= y}.
Proof.
by move=> x_lt0 y z /=; rewrite -levN2 -!scaleNr lev_pscale2l ?oppr_gt0.
Qed.

Lemma ltv_nscale2l a : a < 0 -> {mono ( *:%R a : T -> T) : x y /~ x < y}.
Proof. by move=> x_lt0; apply: leW_nmono (lev_nscale2l _). Qed.

Definition ltev_nscale2l := (lev_nscale2l, ltv_nscale2l).

Lemma lev_wpscale2l a : 0 <= a -> {homo ( *:%R a : T -> T) : y z / y <= z}.
Proof.
by rewrite le0r => /orP[/eqP-> y z | /lev_pscale2l/mono2W//]; rewrite !scale0r.
Qed.

Lemma lev_wpscale2r x : '0 <= x -> {homo *:%R^~ x : y z / (y <= z)%O}.
Proof.
move=>x_ge0 a b; rewrite -subr_ge0 -subv_ge0 -scalerBl le0r.
by move=>/orP[/eqP->|/(pscalev_rge0 x)->//]; rewrite scale0r.
Qed.

Lemma lev_wnscale2l a : a <= 0 -> {homo ( *:%R a : T -> T) : y z /~ y <= z}.
Proof.
by move=> x_le0 y z leyz; rewrite -![a *: _]scalerNN lev_wpscale2l ?ltevNE// lterNE.
Qed.

Lemma lev_wnscale2r x : x <= 0 -> {homo *:%R^~ x : y z /~ (y <= z)%O}.
Proof.
by move=> x_le0 y z leyz; rewrite -![_ *: x]scalerNN lev_wpscale2r ?ltevNE// lterNE.
Qed.

(* Binary forms, for backchaining. *)

Lemma lev_pscale2 a b x y :
  0 <= a -> '0 <= x -> a <= b -> x <= y -> a *: x <= b *: y.
Proof.
move=> x1ge0 x2ge0 le_xy1 le_xy2; have y1ge0 := le_trans x1ge0 le_xy1.
exact: le_trans (lev_wpscale2r x2ge0 le_xy1) (lev_wpscale2l y1ge0 le_xy2).
Qed.

Lemma ltv_pscale2 a b x y :
  0 <= a -> '0 <= x -> a < b -> x < y -> a *: x < b *: y.
Proof.
move=> x1ge0 x2ge0 lt_xy1 lt_xy2; have y1gt0 := le_lt_trans x1ge0 lt_xy1.
by rewrite (le_lt_trans (lev_wpscale2r x2ge0 (ltW lt_xy1))) ?ltv_pscale2l.
Qed.

(* complement for x *+ n and <= or < *)
Local Notation natmul := (@GRing.natmul T).

Lemma lev_pmuln2r n : (0 < n)%N -> {mono natmul^~ n : x y / x <= y}.
Proof.
by case: n => // n _ x y /=; rewrite -!scaler_nat lev_pscale2l ?ltr0n.
Qed.

Lemma ltv_pmuln2r n : (0 < n)%N -> {mono natmul^~ n : x y / x < y}.
Proof. by move/lev_pmuln2r/leW_mono. Qed.

Lemma pmulvnI n : (0 < n)%N -> injective (natmul^~ n).
Proof. by move/lev_pmuln2r/inc_inj. Qed.

Lemma eqr_pmuln2r n : (0 < n)%N -> {mono natmul^~ n : x y / x == y}.
Proof. by move/pmulvnI/inj_eq. Qed.

Lemma pmulvn_lgt0 x n : (0 < n)%N -> ('0 < x *+ n) = ('0 < x).
Proof. by move=> n_gt0; rewrite -(mul0rn _ n) ltv_pmuln2r // mul0rn. Qed.

Lemma pmulvn_llt0 x n : (0 < n)%N -> (x *+ n < 0) = (x < 0).
Proof. by move=> n_gt0; rewrite -(mul0rn _ n) ltv_pmuln2r // mul0rn. Qed.

Lemma pmulvn_lge0 x n : (0 < n)%N -> ('0 <= x *+ n) = ('0 <= x).
Proof. by move=> n_gt0; rewrite -(mul0rn _ n) lev_pmuln2r // mul0rn. Qed.

Lemma pmulvn_lle0 x n : (0 < n)%N -> (x *+ n <= 0) = (x <= 0).
Proof. by move=> n_gt0; rewrite -(mul0rn _ n) lev_pmuln2r // mul0rn. Qed.

Lemma ltv_wmuln2r x y n : x < y -> (x *+ n < y *+ n) = (0 < n)%N.
Proof. by move=> ltxy; case: n=> // n; rewrite ltv_pmuln2r. Qed.

Lemma ltv_wpmuln2r n : (0 < n)%N -> {homo natmul^~ n : x y / x < y}.
Proof. by move=> n_gt0 x y /= / ltv_wmuln2r ->. Qed.

Lemma lev_wMn2r n : {homo natmul^~ n : x y / x <= y}.
Proof. by move=> x y hxy /=; case: n=> // n; rewrite lev_pmuln2r. Qed.

Lemma mulvn_wge0 x n : '0 <= x -> '0 <= x *+ n.
Proof. by move=> /(lev_wMn2r n); rewrite mul0rn. Qed.

Lemma mulvn_wle0 x n : x <= 0 -> x *+ n <= 0.
Proof. by move=> /(lev_wMn2r n); rewrite mul0rn. Qed.

Lemma lev_muln2r n x y : (x *+ n <= y *+ n) = ((n == 0%N) || (x <= y)).
Proof. by case: n => [|n]; rewrite ?lexx ?eqxx // lev_pmuln2r. Qed.

Lemma ltv_muln2r n x y : (x *+ n < y *+ n) = ((0 < n)%N && (x < y)).
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
  '0 <= x -> {homo (natmul x) : m n / (m <= n)%N >-> m <= n}.
Proof. by move=> xge0 m n /subnK <-; rewrite mulrnDr lev_paddl ?mulvn_wge0. Qed.

Lemma lev_wnmuln2l x :
  x <= 0 -> {homo (natmul x) : m n / (n <= m)%N >-> m <= n}.
Proof.
by move=> xle0 m n hmn /=; rewrite -levN2 -!mulNrn lev_wpmuln2l // oppv_cp0.
Qed.

Lemma mulvn_wgt0 x n : '0 < x -> '0 < x *+ n = (0 < n)%N.
Proof. by case: n => // n hx; rewrite pmulvn_lgt0. Qed.

Lemma mulvn_wlt0 x n : x < 0 -> x *+ n < 0 = (0 < n)%N.
Proof. by case: n => // n hx; rewrite pmulvn_llt0. Qed.

Lemma lev_pmuln2l x :
  '0 < x -> {mono (natmul x) : m n / (m <= n)%N >-> m <= n}.
Proof.
move=> x_gt0 m n /=; case: leqP => hmn; first by rewrite lev_wpmuln2l // ltW.
rewrite -(subnK (ltnW hmn)) mulrnDr gev_addr lt_geF //.
by rewrite mulvn_wgt0 // subn_gt0.
Qed.

Lemma ltv_pmuln2l x :
  '0 < x -> {mono (natmul x) : m n / (m < n)%N >-> m < n}.
Proof. by move=> x_gt0; apply: leW_mono (lev_pmuln2l _). Qed.

Lemma lev_nmuln2l x :
  x < 0 -> {mono (natmul x) : m n / (n <= m)%N >-> m <= n}.
Proof.
by move=> x_lt0 m n /=; rewrite -levN2 -!mulNrn lev_pmuln2l // oppv_gt0.
Qed.

Lemma ltv_nmuln2l x :
  x < 0 -> {mono (natmul x) : m n / (n < m)%N >-> m < n}.
Proof. by move=> x_lt0; apply: leW_nmono (lev_nmuln2l _). Qed.

Lemma pmulvn_rgt0 x n : '0 < x -> '0 < x *+ n = (0 < n)%N.
Proof. by move=> x_gt0; rewrite -(mulr0n x) ltv_pmuln2l. Qed.

Lemma pmulvn_rlt0 x n : '0 < x -> x *+ n < 0 = false.
Proof. by move=> x_gt0; rewrite -(mulr0n x) ltv_pmuln2l. Qed.

Lemma pmulvn_rge0 x n : '0 < x -> '0 <= x *+ n.
Proof. by move=> x_gt0; rewrite -(mulr0n x) lev_pmuln2l. Qed.

Lemma pmulvn_rle0 x n : '0 < x -> x *+ n <= 0 = (n == 0)%N.
Proof. by move=> x_gt0; rewrite -(mulr0n x) lev_pmuln2l ?leqn0. Qed.

Lemma nmulvn_rgt0 x n : x < 0 -> '0 < x *+ n = false.
Proof. by move=> x_lt0; rewrite -(mulr0n x) ltv_nmuln2l. Qed.

Lemma nmulvn_rge0 x n : x < 0 -> '0 <= x *+ n = (n == 0)%N.
Proof. by move=> x_lt0; rewrite -(mulr0n x) lev_nmuln2l ?leqn0. Qed.

Lemma nmulvn_rle0 x n : x < 0 -> x *+ n <= 0.
Proof. by move=> x_lt0; rewrite -(mulr0n x) lev_nmuln2l. Qed.

(* Remark : pscalev_rgt0 and pscalev_rge0 are defined above *)

(* a positive and y right *)
Lemma pscalev_rlt0 a y : 0 < a -> (a *: y < 0) = (y < 0).
Proof. by move=> x_gt0; rewrite -!oppv_gt0 -scalerN pscalev_rgt0 // oppr_gt0. Qed.

Lemma pscalev_rle0 a y : 0 < a -> (a *: y <= 0) = (y <= 0).
Proof. by move=> x_gt0; rewrite -!oppv_ge0 -scalerN pscalev_rge0 // oppr_ge0. Qed.

(* a negative and y right *)
Lemma nscalev_rgt0 a y : a < 0 -> ('0 < a *: y) = (y < 0).
Proof. by move=> x_lt0; rewrite -scalerNN pscalev_rgt0 ?ltevNE// lterNE. Qed.

Lemma nscalev_rge0 a y : a < 0 -> ('0 <= a *: y) = (y <= 0).
Proof. by move=> x_lt0; rewrite -scalerNN pscalev_rge0 ?ltevNE// lterNE. Qed.

Lemma nscalev_rlt0 a y : a < 0 -> (a *: y < 0) = ('0 < y).
Proof. by move=> x_lt0; rewrite -scalerNN pscalev_rlt0 ?ltevNE// lterNE. Qed.

Lemma nscalev_rle0 a y : a < 0 -> (a *: y <= 0) = ('0 <= y).
Proof. by move=> x_lt0; rewrite -scalerNN pscalev_rle0 ?ltevNE// lterNE. Qed.

(* weak and symmetric lemmas *)
Lemma scalev_ge0 a y : 0 <= a -> '0 <= y -> '0 <= a *: y.
Proof. by move=> x_ge0 y_ge0; rewrite -(scaler0 _ a) lev_wpscale2l. Qed.

Lemma scalev_le0 a y : a <= 0 -> y <= 0 -> '0 <= a *: y.
Proof. by move=> x_le0 y_le0; rewrite -(scaler0 _ a) lev_wnscale2l. Qed.

Lemma scalev_ge0_le0 a y : 0 <= a -> y <= 0 -> a *: y <= 0.
Proof. by move=> x_le0 y_le0; rewrite -(scaler0 _ a) lev_wpscale2l. Qed.

Lemma scalev_le0_ge0 a y : a <= 0 -> '0 <= y -> a *: y <= 0.
Proof. by move=> x_le0 y_le0; rewrite -(scaler0 _ a) lev_wnscale2l. Qed.

(* scalev_gt0 with only one case *)

Lemma scalev_gt0 a x : 0 < a -> '0 < x -> '0 < a *: x.
Proof. by move=> x_gt0 y_gt0; rewrite pscalev_rgt0. Qed.

Lemma scalev_lt0 a x : a < 0 -> x < 0 -> '0 < a *: x.
Proof. by move=> x_le0 y_le0; rewrite nscalev_rgt0. Qed.

Lemma scalev_gt0_lt0 a x : 0 < a -> x < 0 -> a *: x < 0.
Proof. by move=> x_le0 y_le0; rewrite pscalev_rlt0. Qed.

Lemma scalev_lt0_gt0 a x : a < 0 -> '0 < x -> a *: x < 0.
Proof. by move=> x_le0 y_le0; rewrite nscalev_rlt0. Qed.

(* lev/ltv and multiplication between a positive/negative
   and a exterior (1 <= _) or interior (0 <= _ <= 1) *)

Lemma lev_pescale a x : '0 <= x -> 1 <= a -> x <= a *: x.
Proof. by move=> hy hx; rewrite -{1}[x]scale1r lev_wpscale2r. Qed.

Lemma lev_nescale a x : x <= 0 -> 1 <= a -> a *: x <= x.
Proof. by move=> hy hx; rewrite -{2}[x]scale1r lev_wnscale2r. Qed.

Lemma lev_piscale a x : '0 <= x -> a <= 1 -> a *: x <= x.
Proof. by move=> hy hx; rewrite -{2}[x]scale1r lev_wpscale2r. Qed.

Lemma lev_niscale a x : x <= 0 -> a <= 1 -> x <= a *: x.
Proof. by move=> hy hx; rewrite -{1}[x]scale1r lev_wnscale2r. Qed.

End VOrderFieldTheory.

Section CanVOrderTheory.
Variable (R: numFieldType) (T : canVOrderType R).
Implicit Type (x y z : T) (a b c : R).
Local Notation "'0" := (0 : T).

Lemma pscalev_lgt0 y a : '0 < y -> ('0 < a *: y) = (0 < a).
Proof.
by move=>Py; rewrite !lt_def scaler_eq0 negb_or pscalev_lge0// lt0v_neq0// andbT.
Qed.

Lemma lev_pscale2r x : '0 < x -> {mono *:%R^~ x : x y / (x <= y)%O}.
Proof.
by move=>Px a b; rewrite -subv_ge0 -scalerBl pscalev_lge0// subr_ge0.
Qed.  

Lemma ltv_pscale2r x : '0 < x -> {mono *:%R^~ x : x y / (x < y)%O}.
Proof. by move=> x_gt0; apply: leW_mono (lev_pscale2r _). Qed.

Definition ltev_pscale2r := (lev_pscale2r, ltv_pscale2r).


Lemma lev_nscale2r x : x < 0 -> {mono *:%R^~ x : x y /~ (x <= y)%O}.
Proof.
by move=> x_lt0 y z /=; rewrite -levN2 -!scalerN lev_pscale2r// oppv_gt0.
Qed.

Lemma ltv_nscale2r x : x < 0 -> {mono *:%R^~ x : x y /~ (x < y)%O}.
Proof. by move=> x_lt0; apply: leW_nmono (lev_nscale2r _). Qed.

Definition ltev_nscale2r := (lev_nscale2r, ltv_nscale2r).

(* x positive and y left *)
Lemma pscalev_llt0 x a : '0 < x -> (a *: x < 0) = (a < 0).
Proof. by move=> x_gt0; rewrite -!oppv_gt0 -scaleNr pscalev_lgt0 // oppr_gt0. Qed.

Lemma pscalev_lle0 x a : '0 < x -> (a *: x <= 0) = (a <= 0).
Proof. by move=> x_gt0; rewrite -!oppv_ge0 -scaleNr pscalev_lge0 // oppr_ge0. Qed.

(* x negative and y left *)
Lemma nscalev_lgt0 x a : x < 0 -> ('0 < a *: x) = (a < 0).
Proof. by move=> x_lt0; rewrite -scalerNN pscalev_lgt0 ?ltevNE// lterNE. Qed.

Lemma nscalev_lge0 x a : x < 0 -> ('0 <= a *: x) = (a <= 0).
Proof. by move=> x_lt0; rewrite -scalerNN pscalev_lge0 ?ltevNE// lterNE. Qed.

Lemma nscalev_llt0 x a : x < 0 -> (a *: x < 0) = (0 < a).
Proof. by move=> x_lt0; rewrite -scalerNN pscalev_llt0 ?ltevNE// lterNE. Qed.

Lemma nscalev_lle0 x a : x < 0 -> (a *: x <= 0) = (0 <= a).
Proof. by move=> x_lt0; rewrite -scalerNN pscalev_lle0 ?ltevNE// lterNE. Qed.

(* lev/ltv and multiplication between a positive/negative *)

Lemma gev_pscale a x : '0 < x -> (a *: x <= x) = (a <= 1).
Proof. by move=> hy; rewrite -{2}[x]scale1r lev_pscale2r. Qed.

Lemma gtv_pscale a x : '0 < x -> (a *: x < x) = (a < 1).
Proof. by move=> hy; rewrite -{2}[x]scale1r ltv_pscale2r. Qed.

Lemma lev_pscale a x : '0 < x -> (x <= a *: x) = (1 <= a).
Proof. by move=> hy; rewrite -{1}[x]scale1r lev_pscale2r. Qed.

Lemma ltv_pscale a x : '0 < x -> (x < a *: x) = (1 < a).
Proof. by move=> hy; rewrite -{1}[x]scale1r ltv_pscale2r. Qed.

Lemma gev_nscale a x : x < 0 -> (a *: x <= x) = (1 <= a).
Proof. by move=> hy; rewrite -{2}[x]scale1r lev_nscale2r. Qed.

Lemma gtv_nscale a x : x < 0 -> (a *: x < x) = (1 < a).
Proof. by move=> hy; rewrite -{2}[x]scale1r ltv_nscale2r. Qed.

Lemma lev_nscale a x : x < 0 -> (x <= a *: x) = (a <= 1).
Proof. by move=> hy; rewrite -{1}[x]scale1r lev_nscale2r. Qed.

Lemma ltv_nscale a x : x < 0 -> (x < a *: x) = (a < 1).
Proof. by move=> hy; rewrite -{1}[x]scale1r ltv_nscale2r. Qed.

End CanVOrderTheory.

Definition applyar_head U V W t (f : U -> V -> W) u v := let: tt := t in f v u.
Notation applyar := (@applyar_head _ _ _ tt).

HB.mixin Record isBRegVOrder
 (R: numFieldType) (U V W : vorderType R) (op : U -> V -> W) := {
  badditivel_subproof : forall u', additive (op^~ u');
  badditiver_subproof : forall u, additive (op u);
  bregv_eq0 : forall x y, op x y == 0 = (x == 0) || (y == 0);
  pbregv_rge0 : forall x y, (0 : U) < x -> ((0 : W) <= op x y) = ((0 : V) <= y);
  pbregv_lge0 : forall y x, (0 : V) < y -> ((0 : W) <= op x y) = ((0 : U) <= x);
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

Lemma pbregv_rgt0 a x : l0 < a -> (b0 < f a x) = (r0 < x).
Proof.
move=>xgt0. rewrite !lt0v (pbregv_rge0 _ _ xgt0) bregv_eq0//.
by move: xgt0; rewrite lt_def=>/andP[/negPf->].
Qed.

Lemma pbregv_lgt0 x a : r0 < x -> (b0 < f a x) = (l0 < a).
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

Lemma lev_pbreg2lP a x y : l0 < a -> x <= y -> (f a x) <= (f a y).
Proof. by move=>Pa Pxy; rewrite -subv_ge0 -bregvBr/= pbregv_rge0// subv_ge0. Qed.

(* mulr and lev/ltv *)
Lemma lev_pbreg2l a : l0 < a -> {mono (f a) : x y / x <= y}.
Proof.
by move=> x_gt0 y z /=; rewrite -subv_ge0 -bregvBr pbregv_rge0// subv_ge0.
Qed.

Lemma ltv_pbreg2l a : l0 < a -> {mono (f a) : x y / x < y}.
Proof. by move=> x_gt0; apply: leW_mono (lev_pbreg2l _). Qed.

Definition ltev_pbreg2l := (lev_pbreg2l, ltv_pbreg2l).

Lemma lev_pbreg2r x : r0 < x -> {mono f^~ x : x y / x <= y}.
Proof.
by move=> x_gt0 y z /=; rewrite -subv_ge0 -bregvBl pbregv_lge0// subv_ge0.
Qed.  

Lemma ltv_pbreg2r x : r0 < x -> {mono f^~ x : x y / x < y}.
Proof. by move=> x_gt0; apply: leW_mono (lev_pbreg2r _). Qed.

Definition ltev_pbreg2r := (lev_pbreg2r, ltv_pbreg2r).

Lemma lev_nbreg2l a : a < 0 -> {mono (f a) : x y /~ x <= y}.
Proof.
by move=> x_lt0 y z /=; rewrite -levN2 -!bregvNl/= lev_pbreg2l ?oppv_gt0.
Qed.

Lemma ltv_nbreg2l a : a < 0 -> {mono (f a) : x y /~ x < y}.
Proof. by move=> x_lt0; apply: leW_nmono (lev_nbreg2l _). Qed.

Definition ltev_nbreg2l := (lev_nbreg2l, ltv_nbreg2l).

Lemma lev_nbreg2r x : x < 0 -> {mono f^~ x : x y /~ x <= y}.
Proof.
by move=> x_lt0 y z /=; rewrite -levN2 -!bregvNr lev_pbreg2r// oppv_gt0.
Qed.

Lemma ltv_nbreg2r x : x < 0 -> {mono f^~ x : x y /~ x < y}.
Proof. by move=> x_lt0; apply: leW_nmono (lev_nbreg2r _). Qed.

Definition ltev_nbreg2r := (lev_nbreg2r, ltv_nbreg2r).

Lemma lev_wpbreg2l a : l0 <= a -> {homo (f a) : y z / y <= z}.
Proof.
by rewrite le0v => /orP[/eqP-> y z | /lev_pbreg2l/mono2W//]; rewrite !bregv0l.
Qed.

Lemma lev_wnbreg2l a : a <= 0 -> {homo (f a) : y z /~ y <= z}.
Proof.
by move=> x_le0 y z leyz; rewrite -![f a _]bregvNN lev_wpbreg2l ?ltevNE.
Qed.

Lemma lev_wpbreg2r x : r0 <= x -> {homo f^~ x : y z / y <= z}.
Proof.
by rewrite le0v => /orP[/eqP-> y z | /lev_pbreg2r/mono2W//]; rewrite !bregv0r.
Qed.

Lemma lev_wnbreg2r x : x <= 0 -> {homo f^~ x : y z /~ y <= z}.
Proof.
by move=> x_le0 y z leyz; rewrite -![f _ x]bregvNN lev_wpbreg2r ?ltevNE.
Qed.

(* Binary forms, for backchaining. *)
Lemma lev_pbreg2 a b x y :
  l0 <= a -> r0 <= x -> a <= b -> x <= y -> f a x <= f b y.
Proof.
move=> x1ge0 x2ge0 le_xy1 le_xy2; have y1ge0 := le_trans x1ge0 le_xy1.
exact: le_trans (lev_wpbreg2r x2ge0 le_xy1) (lev_wpbreg2l y1ge0 le_xy2).
Qed.

Lemma ltv_pbreg2 a b x y :
  l0 <= a -> r0 <= x -> a < b -> x < y -> f a x < f b y.
Proof.
move=> x1ge0 x2ge0 lt_xy1 lt_xy2; have y1gt0 := le_lt_trans x1ge0 lt_xy1.
by rewrite (le_lt_trans (lev_wpbreg2r x2ge0 (ltW lt_xy1))) ?ltv_pbreg2l.
Qed.

Lemma pbregv_rlt0 a x : l0 < a -> (f a x < 0) = (x < 0).
Proof. by move=> x_gt0; rewrite -!oppv_gt0 -bregvNr pbregv_rgt0// oppv_gt0. Qed.

Lemma pbregv_rle0 a x : l0 < a -> (f a x <= 0) = (x <= 0).
Proof. by move=> x_gt0; rewrite -!oppv_ge0 -bregvNr pbregv_rge0// oppr_ge0. Qed.

Lemma nbregv_rgt0 a x : a < 0 -> (b0 < f a x) = (x < 0).
Proof. by move=> x_lt0; rewrite -bregvNN pbregv_rgt0 ?ltevNE. Qed.

Lemma nbregv_rge0 a x : a < 0 -> (b0 <= f a x) = (x <= 0).
Proof. by move=> x_lt0; rewrite -bregvNN pbregv_rge0 ?ltevNE. Qed.

Lemma nbregv_rlt0 a x : a < 0 -> (f a x < 0) = (r0 < x).
Proof. by move=> x_lt0; rewrite -bregvNN pbregv_rlt0 ?ltevNE. Qed.

Lemma nbregv_rle0 a x : a < 0 -> (f a x <= 0) = (r0 <= x).
Proof. by move=> x_lt0; rewrite -bregvNN pbregv_rle0 ?ltevNE. Qed.

Lemma pbregv_llt0 x a : r0 < x -> (f a x < 0) = (a < 0).
Proof. by move=> x_gt0; rewrite -!oppv_gt0 -bregvNl pbregv_lgt0// oppv_gt0. Qed.

Lemma pbregv_lle0 x a : r0 < x -> (f a x <= 0) = (a <= 0).
Proof. by move=> x_gt0; rewrite -!oppv_ge0 -bregvNl pbregv_lge0// oppr_ge0. Qed.

Lemma nbregv_lgt0 x a : x < 0 -> (b0 < f a x) = (a < 0).
Proof. by move=> x_lt0; rewrite -bregvNN pbregv_lgt0 ?ltevNE. Qed.

Lemma nbregv_lge0 x a : x < 0 -> (b0 <= f a x) = (a <= 0).
Proof. by move=> x_lt0; rewrite -bregvNN pbregv_lge0 ?ltevNE. Qed.

Lemma nbregv_llt0 x a : x < 0 -> (f a x < 0) = (l0 < a).
Proof. by move=> x_lt0; rewrite -bregvNN pbregv_llt0 ?ltevNE. Qed.

Lemma nbregv_lle0 x a : x < 0 -> (f a x <= 0) = (l0 <= a).
Proof. by move=> x_lt0; rewrite -bregvNN pbregv_lle0 ?ltevNE. Qed.

(* weak and symmetric lemmas *)
Lemma bregv_ge0 a x : l0 <= a -> r0 <= x -> b0 <= f a x.
Proof. by move=> x_ge0 y_ge0; rewrite -(bregv0r a) lev_wpbreg2l. Qed.

Lemma bregv_le0 a x : a <= 0 -> x <= 0 -> b0 <= f a x.
Proof. by move=> x_le0 y_le0; rewrite -(bregv0r a) lev_wnbreg2l. Qed.

Lemma bregv_ge0_le0 a x : l0 <= a -> x <= 0 -> f a x <= 0.
Proof. by move=> x_le0 y_le0; rewrite -(bregv0r a) lev_wpbreg2l. Qed.

Lemma bregv_le0_ge0 a x : a <= 0 -> r0 <= x -> f a x <= 0.
Proof. by move=> x_le0 y_le0; rewrite -(bregv0r a) lev_wnbreg2l. Qed.

(* bregv_gt0 with only one case *)

Lemma bregv_gt0 a x : l0 < a -> r0 < x -> b0 < f a x.
Proof. by move=> x_gt0 y_gt0; rewrite pbregv_rgt0. Qed.

Lemma bregv_lt0 a x : a < 0 -> x < 0 -> b0 < f a x.
Proof. by move=> x_le0 y_le0; rewrite nbregv_rgt0. Qed.

Lemma bregv_gt0_lt0 a x : l0 < a -> x < 0 -> f a x < 0.
Proof. by move=> x_le0 y_le0; rewrite pbregv_rlt0. Qed.

Lemma bregv_lt0_gt0 a x : a < 0 -> r0 < x -> f a x < 0.
Proof. by move=> x_le0 y_le0; rewrite nbregv_rlt0. Qed.

End BRegVOrderTheory.

(* here, we only define l2norm, for general case, see mxnorm.v *)
Section l2normC.
Variable (R: numClosedFieldType) (m n: nat).
Implicit Type (A B : 'M[R]_(m,n)).

Definition l2normC A := 2.-root (\sum_i `|A i.1 i.2| ^+ 2).

Lemma l2normC_pair A : l2normC A = 2.-root (\sum_i\sum_j (`|A i j| ^+ 2)).
Proof. by f_equal; rewrite pair_bigA. Qed.

Lemma l2normC0_eq0 : forall A, l2normC A = 0 -> A = 0.
Proof.
move=>A /eqP; rewrite rootC_eq0// =>/eqP.
have P1 i: true -> 0 <= `|A i.1 i.2| ^+ 2 by move=>_; apply/exprn_ge0/normr_ge0.
move/(psumr_eq0P P1)=>P2; apply/matrixP=>i j; move: (P2 (i,j) isT)=>/eqP.
by rewrite mxE expf_eq0/= normr_eq0=>/eqP.
Qed.

Lemma l2normCZ a A : l2normC (a *: A) = `|a| * l2normC A.
Proof.
rewrite -(rootCK (ltn0Sn 1) `|a|) /l2normC -rootCX// -rootCMl ?exprn_ge0//.
f_equal; rewrite mulr_sumr; apply eq_bigr=>i _.
by rewrite !mxE normrM exprMn.
Qed.

Lemma l2normC_triangle A B : l2normC (A + B) <= l2normC A + l2normC B.
Proof.
rewrite /l2normC; under eq_bigr do rewrite mxE.
apply: discrete_Minkowski_inequality.
Qed.

HB.instance Definition _ := isVNorm.Build R 'M_(m, n) l2normC
  l2normC_triangle l2normC0_eq0 l2normCZ.

Lemma l2normC_ge0 A : l2normC A >= 0. Proof. exact: normv_ge0. Qed.

Lemma dotV_l2normC (M: 'M[R]_(m,n)) : \tr (M ^*t *m M) = l2normC M ^+2.
Proof.
rewrite /l2normC sqrtCK -(pair_bigA _ (fun x y=> `|M x y| ^+2))/= exchange_big.
rewrite /mxtrace; apply eq_bigr=>i _; rewrite !mxE; apply eq_bigr=>j _.
by rewrite !mxE normCKC.
Qed.

Lemma dot_l2normC (M: 'M[R]_(m,n)) : \tr (M *m M ^*t) = l2normC M ^+2.
Proof. by rewrite -dotV_l2normC mxtrace_mulC. Qed.

Lemma l2normC_dotV (M: 'M[R]_(m,n)) : l2normC M = sqrtC (\tr (M ^*t *m M)).
Proof. by rewrite dotV_l2normC exprCK// normv_ge0. Qed.

Lemma l2normC_dot (M: 'M[R]_(m,n)) : l2normC M = sqrtC (\tr (M *m M ^*t)).
Proof. by rewrite l2normC_dotV mxtrace_mulC. Qed.

Lemma l2normCUl (U : 'M[R]_m) (M : 'M[R]_(m,n)): 
  U \is unitarymx -> l2normC (U *m M) = l2normC M.
Proof.
by move=>P; rewrite l2normC_dot !adjmxM -!mulmxA 
mxtrace_mulC mulmxA mulmxKtV// -l2normC_dot.
Qed.

Lemma l2normC_unitary (U : 'M[R]_(m,n)) :
  U \is unitarymx -> l2normC U = sqrtC m%:R.
Proof. by move=>/unitarymxP PU; rewrite l2normC_dot PU mxtrace1. Qed.

End l2normC.

#[global] Hint Extern 0 (is_true (0 <= l2normC _)) => apply: l2normC_ge0 : core.

Section l2normC_extra.
Variable (C : numClosedFieldType).

Lemma l2normC_trmx m n (A : 'M[C]_(m,n)) : l2normC (A^T) = l2normC A. 
Proof. 
rewrite !l2normC_pair; f_equal; rewrite exchange_big.
by under eq_bigr do under eq_bigr do rewrite mxE.
Qed.

Lemma l2normC_adjmx m n (A : 'M[C]_(m,n)) : l2normC (A^*t) = l2normC A.
Proof. by rewrite -l2normC_trmx /l2normC; under eq_bigr do rewrite !mxE norm_conjC.  Qed.

Lemma l2normC_conjmx m n (A : 'M[C]_(m,n)) : l2normC (A^*m) = l2normC A.
Proof. by rewrite -l2normC_adjmx adjmxCT conjmxK l2normC_trmx. Qed.

Lemma l2normCUr m n l (U : 'M[C]_(n,l)) (M : 'M_(m,n)): 
  U \is unitarymx -> l2normC (M *m U) = l2normC M.
Proof.
by move=>P; rewrite l2normC_dot !adjmxM !mulmxA mulmxtVK// -l2normC_dot.
Qed.

Lemma l2normC_cauchy m (u : 'rV[C]_m) (v : 'cV[C]_m) :
  `| \tr (u *m v) | <= l2normC u * l2normC v.
Proof.
rewrite trace_mx11 mxE -(ler_pXn2r (n := 2))// ?nnegrE// ?mulr_ge0// ?normv_ge0//.
apply/(le_trans (Cauchy_Schwarz_C _ _ _ _)).
by rewrite exprMn !sqrtCK !pair_bigV/= big_ord1 exchange_big big_ord1.
Qed.

Lemma form_tr_ge0 n m (A : 'M[C]_(m,n)) : 0 <= \tr (A *m A^*t ).
Proof. by rewrite dot_l2normC exprn_ge0. Qed.

Lemma form_tr_eq0 n m (A : 'M[C]_(m,n)) : \tr (A *m A^*t ) = 0 -> A = 0.
Proof. by move=>/eqP; rewrite dot_l2normC expf_eq0/= normv_eq0=>/eqP. Qed.

Lemma formV_tr_ge0 n m (A : 'M[C]_(m,n)) : 0 <= \tr (A^*t *m A ).
Proof. by rewrite mxtrace_mulC form_tr_ge0. Qed.

Lemma formV_tr_eq0 n m (A : 'M[C]_(m,n)) : \tr (A^*t *m A ) = 0 -> A = 0.
Proof. rewrite mxtrace_mulC; exact: form_tr_eq0. Qed.

End l2normC_extra.

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
move: (psdmxD P2 P1); by rewrite addrA addrNK.
Qed.

(* Fact vorder_display : unit. Proof. exact: tt. Qed. *)
(* why using vorder_display fails to use <=? *)
HB.instance Definition _ n := Order.Le_isPOrder.Build ring_display 'M[C]_n
  (@lownerle_refl n) (@lownerle_anti n) (@lownerle_trans n).
(* HB.instance Definition _ n := Order.isPOrder.Build ring_display 'M[C]_n
  (@lownerlt_def n) (@lownerle_refl n) (@lownerle_anti n) (@lownerle_trans n). *)

HB.instance Definition _ n := [SubChoice_isSubPOrder of 'MDen[C]_n by <: with ring_display].

(* HB.instance Definition _ n : Order.SubPOrder ring_display _ := [POrder of 'MDen[C]_n by <:]. *)

Lemma le_lownerE n (x y : 'M[C]_n) : x <= y = ((y - x) \is psdmx).
Proof. by rewrite /@Order.le/= /lownerle. Qed.

Lemma lemx_add2rP n (z x y : 'M[C]_n) : x <= y -> x + z <= y + z.
Proof. by rewrite !le_lownerE opprD addrACA addrN addr0. Qed.

Lemma lemx_pscale2lP n (e : C) (x y : 'M[C]_n) : 0 < e -> x <= y -> e *: x <= e *: y.
Proof.
rewrite !le_lownerE -scalerBr. set z := y - x.
move=>P1 /psdmx_dot P2. apply/psdmx_dot=>u. move: (P2 u).
rewrite linearZ/= -scalemxAl linearZ/= !nnegrE=>P3.
apply: (mulr_ge0 _ P3). by apply/ltW.
Qed.

HB.instance Definition _ n := POrderedLmodule_isVOrder.Build C 'M[C]_n (@lemx_add2rP n) (@lemx_pscale2lP n).

Lemma pscalemx_lge0 n (x : 'M[C]_n) (a : C) : 
  (0 : 'M[C]_n) < x -> (0 : 'M[C]_n) <= a *: x = (0 <= a).
Proof.
move=>xgt0. apply/Bool.eq_iff_eq_true; split; last first.
by move=>age0; apply: scalev_ge0=>//; apply/ltW.
move: xgt0. rewrite lt_def {1 2}/Order.le/= /lownerle !subr0.
move =>/andP[/eqP Px /psdmx_dot px]/psdmx_dot pax.
case E : (0 <= a)=>//; exfalso.
apply/Px/eqP/mx_dot_eq0=>u.
move: (px u) (pax u); rewrite !nnegrE -scalemxAr -scalemxAl linearZ/=.
rewrite le_eqVlt=>/orP[/eqP<-//|P1].
by rewrite pmulr_lge0// E.
Qed.

HB.instance Definition _ n := VOrder_isCan.Build C 'M[C]_n (@pscalemx_lge0 n).

Lemma lemx_adj n (M N : 'M_n) : M^*t <= N^*t = (M <= N).
Proof. by rewrite !le_lownerE -linearB/= psdmx_adj. Qed.

Lemma lemx_conj n (M N : 'M_n) : M^*m <= N^*m = (M <= N).
Proof. by rewrite !le_lownerE -linearB/= psdmx_conj. Qed.

Lemma lemx_tr n (M N : 'M_n) : M^T <= N^T = (M <= N).
Proof. by rewrite !le_lownerE -linearB/= psdmx_tr. Qed.

Lemma lemx_trace m (M N : 'M[C]_m) : M <= N -> \tr M <= \tr N.
Proof.
rewrite le_lownerE=>/psdmx_dot P1.
rewrite -subr_ge0 -linearB/= /mxtrace. apply sumr_ge0=>i _.
move: (P1 (delta_mx i 0)). rewrite nnegrE /mxtrace big_ord1.
rewrite adjmx_delta mxE (bigD1 i)//= big1; last first.
rewrite mxE (bigD1 i)//= big1; last first.
by rewrite !mxE !eqxx mulr1 mul1r !addr0.
all: by move=>k /negPf Pf; rewrite !mxE Pf ?eqxx ?mul0r ?mulr0.
Qed.

Lemma ptrace2_psd m n (A : 'M[C]_(m * n)) :
  A \is psdmx -> ptrace2 A \is psdmx.
Proof.
move=>/psdmx_dot P1; rewrite/ptrace2 castmx_funE; apply/psdmx_dot=>u.
rewrite mulmx_sumr mulmx_suml linear_sum nnegrE sumr_ge0// => i _/=.
move: (P1 ((1%:M *t delta_mx i 0) *m u)).
by rewrite adjmxM adjmx_tens adjmx1 adjmx_delta nnegrE !mulmxA.
Qed.

Lemma ptrace1_psd m n (A : 'M[C]_(m * n)) :
  A \is psdmx -> ptrace1 A \is psdmx.
Proof.
move=>/psdmx_dot P1; rewrite/ptrace2 castmx_funE; apply/psdmx_dot=>u.
rewrite mulmx_sumr mulmx_suml linear_sum nnegrE sumr_ge0// => i _/=.
move: (P1 ((delta_mx i 0 *t 1%:M) *m u)).
by rewrite adjmxM adjmx_tens adjmx1 adjmx_delta nnegrE !mulmxA.
Qed.

Lemma ptrace2_le m n (A B : 'M[C]_(m * n)):
  A <= B -> (ptrace2 A <= ptrace2 B).
Proof. rewrite !le_lownerE -linearB/=. exact: ptrace2_psd. Qed.

Lemma ptrace1_le m n (A B : 'M[C]_(m * n)):
  A <= B -> (ptrace1 A <= ptrace1 B).
Proof. rewrite !le_lownerE -linearB/=. exact: ptrace1_psd. Qed.

End LownerPOrder.
End MxLownerOrder.
Import MxLownerOrder.

Lemma castmx_eq1 (R : ringType) m m' (eqm : m = m') (A: 'M[R]_m) :
  castmx (eqm,eqm) A == 1%:M = (A == 1%:M).
Proof. by case: m' / eqm. Qed.

Lemma castmx_le1 (R : numClosedFieldType) m m' (eqm : m = m') (A: 'M[R]_m) :
  castmx (eqm,eqm) A <= 1%:M = (A <= 1%:M).
Proof. by case: m' / eqm. Qed.

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
  reflect (forall x, x \is psdmx -> \tr (A *m x) <= \tr (B *m x)) (A <= B).
Proof.
rewrite le_lownerE. 
apply/(iffP (@psdmx_dot _ _ _))=>[P x /diag_decomp_absorb ->|P x].
rewrite !mulmx_sumr !linear_sum/= ler_sum // => i _.
by rewrite -subr_ge0 -linearB -mulmxBl/= mulmxA mxtrace_mulC -nnegrE mulmxA P.
rewrite -mulmxA mxtrace_mulC -mulmxA nnegrE mulmxBl linearB/= subr_ge0.
apply P. apply form_psd.
Qed.

Lemma mxtrace_deltaE m (A : 'M[R]_m) : 
  \tr A = \sum_i \tr (delta_mx 0 i *m A *m delta_mx i 0 : 'rV_1).
Proof.
rewrite {1}/mxtrace; apply eq_bigr=>/= i _.
by rewrite trace_mx11 delta_mx_mulEl delta_mx_mulEr eqxx !mul1r.
Qed.

Lemma psdmx_trace m (A : 'M[R]_m) : A \is psdmx -> 0 <= \tr A.
Proof.
move=>/psdmx_dot PA.
by rewrite mxtrace_deltaE sumr_ge0//==>i _; rewrite -nnegrE -adjmx_delta.
Qed.

Lemma psdmx_trace_eq0 m (A : 'M[R]_m) : 
  A \is psdmx -> (\tr A == 0) = (A == 0).
Proof.
move=>PA; apply eqb_iff; split; last by move=>/eqP->; rewrite linear0.
move: {+}PA=>/psdmxP[]/hermitian_normalmx/eigen_dec=>{2 3}-> Pd.
rewrite mxtrace_mulC mulmxA unitarymxKV// mul1mx.
rewrite mxtrace_diag psumr_eq0//=.
  by move=>i _; rewrite -nnegrE; apply/nnegmxP.
move=>/allP Pi.
suff -> : spectral_diag A = 0 by rewrite linear0 mulmx0 mul0mx. 
apply/matrixP=>? i; rewrite ord1 mxE.
by apply/eqP/Pi; rewrite mem_index_enum.
Qed.

Lemma le_lownerE_dentr m (A B: 'M[R]_m) : 
  reflect (forall x, x \is denmx -> \tr (A *m x) <= \tr (B *m x)) (A <= B).
Proof.
apply/(iffP (@le_lownerE_psdtr _ _ _))=>H x Px.
apply H. by apply/denmx_psd.
case E: (x == 0); first by move/eqP: E=>->; rewrite !linear0.
have P: 0 < \tr x.
  by rewrite lt_def psdmx_trace// andbT psdmx_trace_eq0// E.
have : (\tr x)^-1 *: x \is denmx. apply/denmxP. split. 
apply psdmxZ=>//. by rewrite invr_ge0 ltW.
by rewrite linearZ/= mulVf// gt_eqF.
move=>/H. rewrite -!scalemxAr !linearZ/= mulrC [_^-1*_]mulrC ler_pdivrMr//.
by rewrite mulfVK// gt_eqF.
Qed.

End DecPsdmx.
