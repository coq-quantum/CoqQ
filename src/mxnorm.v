(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra complex perm path.
Require Import forms spectral cpo.
From mathcomp.analysis Require Import reals signed.
From mathcomp.real_closed Require Import complex.
From mathcomp.analysis Require Import boolp topology classical_sets normedtype sequences.

Require Import mcextra mxpred mxtopology hermitian.

(* -------------------------------------------------------------------- *)
Import Order.TTheory GRing.Theory Num.Theory ComplexField Num.Def complex.
Import VNorm.
(* -------------------------------------------------------------------- *)
Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.

(****************************************************************************)
(* add matrix norms:                                                        *)
(* pnorm p : eq0 ge0 Z, lack triangle inequality                            *)
(* schattennorm p : eq0 ge0 Z, lack triangle inequality                     *)
(* following are proved as norm, canonical to normv (for all matrices)      *)
(* l1norm := pnorm 1; l2norm := pnorm 2                                     *)
(* i2norm : induced 2-norm                                                  *)
(* fbnorm := schattennorm 2 : Frobenius norm                                *)
(* trnorm := schattennorm 1 : trace/nuclear norm                            *)
(****************************************************************************)
(* provide the svd decomposition : A = 'M[R]_(m,n)  R: numClosedFieldType   *)
(* A = svd_u A *m cdiag_mx (svd_d A) *m (svd_v A)^*t                        *)
(* where svd_u A and svd_v A are two square unitary matrices                *)
(* (svd_d A) is 'rV[R]_(minn m n), with nonincreasing order of singular     *)
(* values cdiag_mx gives the m * n matrix with diagonal elements of D (0    *) 
(* for extended part, i.e., index out of minn m n)                          *)
(* if A is square matrix, A = svd_u A *m diag_mx (svds_d A) *m (svd_v A)^*t *)
(****************************************************************************)
(* Define lowner order; prove density matrix forms cpo                      *)
(****************************************************************************)

(****************************************************************************)
(* frequently used qualifier:                                               *)
(* qualifier 1: over numDomainType, 'M_(n,m)                                *)
(*              nnegmx :=: each elements is Num.nneg                        *)
(* qualifier 0: over numClosedFieldType, 'M_n                               *)
(*         is_svd_diag :=: 'rV with nonincreasing order of nneg elements    *)
(*            normalmx :=: M *m M^*t == M^*t *m M                           *)
(*           unitarymx :=: M *m M^*t == 1%:M                                *)
(*              hermmx :=: M == M^*t                                        *)
(*              diagmx :=: [forall i, forall j, i != j ==> M i j == 0]      *)
(*               psdmx :=: positive semi-definite matrix                    *)
(*               denmx :=: psdmx & \tr M <= 1                               *)
(*               obsmx :=: psdmx & \tr M == 1                               *)
(****************************************************************************)

Section inequality.
Variable (R: numClosedFieldType).

Lemma abs_discriminant_ler0 (a b c : R) : 
  (forall (x : R), x \is Num.real -> `|a| * x ^+2 + `|b| * x + `|c| >= 0)
  -> `|b|^+2 <= 4%:R * `|a| * `|c|.
Proof.
move=>P; case E: (a == 0). case F: (b == 0).
by move/eqP: F=>->; rewrite normr0 expr0n/=; do ? apply mulr_ge0.
have /P: (-`|b| - `|c|/`|b|) \is Num.real by rewrite realE; apply/orP; right;
  rewrite -oppr_ge0 opprB opprK addr_ge0// divr_ge0//.
by move/eqP: E=>->; rewrite normr0 mul0r mulrDr mulrN mulrCA mulrV ?unitfE 
  ?normr_eq0 ?F// mulr1 add0r addrNK mulrN ler_oppr oppr0 mulr0 mul0r expr2.
have /P: (- `|b| / (2%:R * `|a|)) \is Num.real by rewrite realE; apply/orP; 
  right; rewrite -oppr_ge0 mulNr opprK divr_ge0// mulr_ge0//.
rewrite mulNr sqrrN mulrN expr2 [ `|a| * _]mulrA -mulrBl.
have P0: `|a| \is a GRing.unit by rewrite unitfE normr_eq0 E.
have ->: (`|a| * (`|b| / (2%:R * `|a|)) - `|b|) = - `|b| / (2%:R).
by rewrite mulrCA invrM// ?unitfE ?pnatr_eq0// [ `|a| * _]mulrA mulrV// 
  mulrA mulr1 {2}(mathcomp_extra.splitr `|b|) opprD addrA addrN add0r mulNr.
rewrite addrC !mulNr subr_ge0 mulrA ler_pdivr_mulr.
by apply mulr_gt0=>//; rewrite normr_gt0 E.
rewrite mulrC mulrA expr2 ler_pdivr_mulr ?ltr0Sn// =>P1.
by apply (le_trans P1); rewrite mulrC [ `|c| * _]mulrC !mulrA -natrM lexx.
Qed.

Lemma discriminant2_ler0 (a b c : R) : a >= 0 -> c >= 0 ->
(forall (x : R), x \is Num.real -> a * x ^+2 + 2%:R * `|b| * x + c >= 0)
-> `|b|^+2 <= a * c.
Proof.
move/normr_idP=><- /normr_idP<-.
have P0: 2%:R * `|b| = `|2%:R * b| by rewrite normrM ger0_norm// ler0n.
rewrite P0=>/abs_discriminant_ler0. 
by rewrite -P0 !expr2 mulrA [_ * `|b| * _]mulrC mulrA -natrM -!mulrA 
  -ler_pdivl_mull ?ltr0Sn// !mulrA mulVr ?unitfE ?pnatr_eq0// mul1r.
Qed.

Lemma Cauchy_Schwarz_C I (r: seq I) (P: pred I) (X Y : I -> R) :
  (\sum_(i <- r | P i) `|X i|^+2) * (\sum_(i <- r | P i) `|Y i|^+2) 
    >= `| \sum_(i <- r | P i) X i * Y i|^+2.
Proof.
apply (@le_trans _ _ (`|\sum_(i <- r | P i) `|X i| * `|Y i| | ^+ 2)).
apply ler_expn2r; rewrite ?nnegrE// [X in _ <= X]ger0_norm.
by apply sumr_ge0=>i _; apply mulr_ge0.
by apply: (le_trans (ler_norm_sum _ _ _)); under eq_bigr do rewrite normrM.
apply discriminant2_ler0=>[||x Px].
1,2: apply sumr_ge0=>i _; rewrite -realEsqr//.
have P1: 0 <= \sum_(i <- r | P i) (`|X i| * x + `|Y i|)^+2 
  by apply sumr_ge0=>i _; rewrite -realEsqr realD// realM.
apply (le_trans P1). rewrite le_eqVlt; apply/orP; left; apply/eqP.
under eq_bigr do rewrite sqrrD -mulr_natl mulrAC mulrA expr2 mulrACA -!expr2.
rewrite !big_split/= -!mulr_suml -mulr_sumr; congr (_ + _ * _ * _ + _).
by rewrite ger0_norm// sumr_ge0// =>i _; apply mulr_ge0.
Qed.

Lemma normr_sqr_ler_sum (I : finType) (P: pred I) (X : I -> R) :
  (\sum_(i | P i) `|X i|^+2) <= (\sum_(i | P i) `|X i|)^+2.
Proof.
rewrite expr2 big_distrlr/= ler_sum// =>i Pi.
by rewrite (bigD1 i)//= -expr2 ler_paddr// sumr_ge0// =>j _; rewrite mulr_ge0.
Qed.

End inequality.


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
move: (De i j)=>/eqP; rewrite /dexpmx !mxE eqr_expn2//.
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

Lemma unitarymxK m  (U : 'M[R]_m) : U \is unitarymx -> U *m U ^*t = 1%:M.
Proof. by move/unitarymxP. Qed.

Lemma unitarymxKV m  (U : 'M[R]_m) : U \is unitarymx -> U ^*t *m U = 1%:M.
Proof. by move/unitarymxPV. Qed.

Hint Resolve spectral_unitarymx : core.

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
move: (normalmx_const n a)=>/unitarymx_spectralP/esym.
by rewrite mulmxU// mulUCmx// -{3}scalemx1 -scalemxAl mul1mx -scalemxAr 
  unitarymxK// scalemx1 -{2}diag_const_mx=>/diag_mx_inj.
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
Proof. by rewrite qualifE pnorm_ge0. Qed.

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

(* Lemma pnorm_triangle A B : pnorm (A + B) <= pnorm A + pnorm B.
not able to prove it *)

End PNorm.

Definition l1norm (R: numClosedFieldType) (m n: nat) := (@pnorm R 0 m n).
Definition l2norm (R: numClosedFieldType) (m n: nat) := (@pnorm R 1 m n).

Section L1L2Norm.
Variable (R: numClosedFieldType) (m n: nat).
Local Notation M := 'M[R]_(m,n).

Lemma l1norm_ge0 : forall (A : M), l1norm A >= 0. Proof. exact: pnorm_ge0. Qed.
Lemma l1norm_nneg (A : M) : l1norm A \is Num.nneg. Proof. exact: pnorm_nneg. Qed.
Lemma l2norm_ge0 : forall (A : M), l2norm A >= 0. Proof. exact: pnorm_ge0. Qed.
Lemma l2norm_nneg (A : M) : l2norm A \is Num.nneg. Proof. exact: pnorm_nneg. Qed.
Local Hint Resolve l1norm_nneg : core.
Local Hint Resolve l2norm_nneg : core.
Local Hint Resolve l1norm_ge0 : core.
Local Hint Resolve l2norm_ge0 : core.

Lemma pnorm_0n p q (M: 'M[R]_(0,q)) : pnorm p M = 0.
Proof. by rewrite pnorm_pair big_ord0 rootC0. Qed.

Lemma pnorm_n0 p q (M: 'M[R]_(q,0)) : pnorm p M = 0.
Proof. by rewrite pnorm_pair exchange_big big_ord0 rootC0. Qed.

Lemma pnorm_trmx p q r (M: 'M[R]_(q,r)) : pnorm p (M^T) = pnorm p M.
Proof.
rewrite !pnorm_pair; f_equal; rewrite exchange_big.
by under eq_bigr do under eq_bigr do rewrite mxE.
Qed.

Lemma pnorm_adjmx p q r (M: 'M[R]_(q,r)) : pnorm p (M^*t) = pnorm p M.
Proof. by rewrite -pnorm_trmx /pnorm; under eq_bigr do rewrite !mxE norm_conjC. Qed.

Lemma pnorm_conjmx p q r (M: 'M[R]_(q,r)) : pnorm p (M^*m) = pnorm p M.
Proof. by rewrite -pnorm_adjmx adjmxEl conjmxK pnorm_trmx. Qed.

Lemma pnorm_diag p q (D : 'rV[R]_q) : pnorm p (diag_mx D) = pnorm p D.
Proof.
rewrite !pnorm_pair big_ord1; f_equal; apply eq_bigr=>i _.
rewrite (bigD1 i)//= big1 ?mxE ?eqxx ?mulr1n ?addr0// =>j /negPf nji.
by rewrite mxE eq_sym nji mulr0n normr0 expr0n.
Qed.

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
Proof.
rewrite /l1norm /pnorm !root1C -big_split/=; apply ler_sum=>i _.
by rewrite !expr1 mxE ler_norm_add.
Qed.

Lemma l2norm_triangle (A B : 'M[R]_(m,n)) : l2norm (A + B) <= l2norm A + l2norm B.
Proof.
rewrite -(ler_pexpn2r (ltn0Sn 1))//; first by apply addr_ge0.
rewrite /l2norm sqrrD !sqrtCK.
apply (@le_trans _ _ (\sum_i (`|A i.1 i.2| + `|B i.1 i.2|) ^+ 2)).
by apply ler_sum=>i _; rewrite ler_expn2r// ?nnegrE// ?addr_ge0// mxE ler_norm_add.
under eq_bigr do rewrite sqrrD. rewrite !big_split/= ler_add2r ler_add2l 
  -mulr2n ler_wmuln2r// -[X in X <= _]ger0_norm ?sumr_ge0//.
rewrite -(@ler_pexpn2r _ 2)// ?nnegrE// ?mulr_ge0// ?sqrtC_ge0 ?sumr_ge0//.
rewrite exprMn !sqrtCK; apply: (le_trans (Cauchy_Schwarz_C _ _ _ _)).
rewrite le_eqVlt; apply/orP; left; apply/eqP.
by congr (_ * _); under eq_bigr do rewrite normr_id.
Qed.

Lemma l2norm_l1norm (A: 'M[R]_(m,n)) : l2norm A <= l1norm A.
Proof.
rewrite -(ler_pexpn2r (ltn0Sn 1)) ?pnorm_nneg// /l1norm /l2norm /pnorm 
  sqrtCK root1C [in X in _ <= X](eq_bigr (fun i=>`|A i.1 i.2|)).
by move=>i _; rewrite expr1. apply normr_sqr_ler_sum.
Qed.

Lemma l1norm_l2norm (A: 'M[R]_(m,n)) : l1norm A <= sqrtC (m * n)%:R * l2norm A.
Proof.
rewrite -(ler_pexpn2r (ltn0Sn 1)) ?nnegrE ?mulr_ge0 ?pnorm_ge0// ?sqrtC_ge0 
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
Proof. by move=>P; rewrite l2norm_dot !adjmxM -!mulmxA 
mxtrace_mulC mulmxA mulmxKtV// -l2norm_dot. Qed.

Lemma l2normUr (U : 'M[R]_n) (M : 'M[R]_(m,n)): 
  U \is unitarymx -> l2norm (M *m U) = l2norm M.
Proof. by move=>P; rewrite l2norm_dot !adjmxM !mulmxA mulmxtVK// -l2norm_dot. Qed.

Lemma l2norm_deltamx i j : l2norm (delta_mx i j : 'M[R]_(m,n)) = 1.
Proof.
rewrite /l2norm pnorm_pair (bigD1 i)//= (bigD1 j)//= !big1.
1,2: move=>k /negPf nk. 2: rewrite big1// =>l _.
1,2: by rewrite mxE nk/= ?andbF normr0 expr0n.
by rewrite mxE !eqxx normr1 expr1n !addr0 sqrtC1.
Qed.

Canonical l1norm_vnorm := Vnorm l1norm_triangle (@pnorm0_eq0 _ 0 _ _) (@pnormZ _ 0 _ _).
Canonical l2norm_vnorm := Vnorm l2norm_triangle (@pnorm0_eq0 _ 1 _ _) (@pnormZ _ 1 _ _).

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
exists (fingroup.invg p). apply/matrixP=>i j.
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
apply/tuple_permP. exists (fingroup.invg p). f_equal.
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
exists (fingroup.invg p)=>i. 
rewrite -(tnth_ord_tuple (fingroup.invg p i)) -tnth_map -/sf/= (tnth_nth 0) Pp.
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

Lemma trC_perm_mx (s : 'S_n) : (@perm_mx R n s)^*t = perm_mx (fingroup.invg s).
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
by rewrite !mxE ler_pexpn2r// P2 orbT.
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
by rewrite !mxE ler_wpmul2l// orbT.
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
rewrite /cdiag_mx adjmx_cast/= adjmxE tr_block_mx map_block_mx !raddf0 -adjmxE 
  diag_mx_adj; apply/(canLR (castmxKV _ _))=>/=; rewrite castmx_comp.
move: (etrans (min_idl q p) (esym (min_idr p q)))=>E1.
move: (etrans (min_idr q p) (esym (min_idl p q))) (minnC p q) =>E2 E3.
by case: (minn q p) / E3 E1 E2=> E1 E2; rewrite !castmx_id.
Qed.

Lemma cdiag_conjmx p q (D : 'rV[R]_(minn p q)) :
 (cdiag_mx D)^*m = cdiag_mx (D^*m).
Proof. by rewrite /cdiag_mx conjmx_cast conjmxE map_block_mx !raddf0 map_diag_mx. Qed.

Lemma cdiag_trmx p q (D : 'rV[R]_(minn p q)) :
 (cdiag_mx D)^T = cdiag_mx (castmx (erefl _, minnC _ _) D).
Proof. by rewrite -[LHS]conjmxK -adjmxEr cdiag_adjmx cdiag_conjmx conjmx_cast conjmxK. Qed.

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
Proof. by rewrite /svd_d_exdr conjmx_cast !conjmxE map_row_mx raddf0. Qed.

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

Lemma cdiag_mx_mull p q (D D': 'rV[R]_(minn p q)) :
  (cdiag_mx D) *m (cdiag_mx D')^*t = diag_mx ((svd_d_exdl D) .* (svd_d_exdl D' ^*m)).
Proof.
rewrite /cdiag_mx adjmx_cast/= castmx_mul adjmxE tr_block_mx map_block_mx !raddf0/=.
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
rewrite /cdiag_mx adjmx_cast/= castmx_mul adjmxE tr_block_mx map_block_mx !raddf0/=.
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
Canonical cdiag_mx_linear p q := Linear (@cdiag_mx_is_linear p q).

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
apply/psdmx_dot=>v. set u := M *m v ^*t.
have ->: v *m (M ^*t *m M) *m v ^*t = u ^*t *m u.
by rewrite /u adjmxM adjmxK !mulmxA.
by rewrite nnegrE dotV_l2norm exprn_ge0// pnorm_ge0.
Qed.

Lemma form_psd p q (M : 'M[R]_(p,q)) : (M *m M ^*t) \is psdmx.
Proof. by rewrite -{1}(adjmxK M) formV_psd. Qed.

Lemma psdmx_svd p (M : 'M[R]_p) : M \is psdmx -> (exists sdpsd : 'M_p * 'rV_p, 
  [&& (sdpsd.1 \is unitarymx),  (sdpsd.2 \is is_svd_diag) &
  (M == sdpsd.1^*t *m diag_mx sdpsd.2 *m sdpsd.1)]).
Proof.
move=>/psdmxP [/hermmx_normal/unitarymx_spectralP P1 /descreasing_row_vec [s Ps]].
exists (perm_mx s *m spectralmx M, col_perm s (spectral_diag M))=>/=.
apply/and3P; split=>//.
  apply/mul_unitarymx; [apply/perm_mx_unitary | apply/spectral_unitarymx].
by rewrite diag_perm adjmxM !mulmxA !mulmxKtV// ?perm_mx_unitary//; apply/eqP.
Qed.

Lemma dot_dotmxE p q (A B : 'M[R]_(p,q)) i j : 
  (A *m B ^*t) i j = '[ (row i A), (row j B)].
Proof. by rewrite dotmxE !mxE; apply eq_bigr=>k _; rewrite !mxE. Qed.

Lemma mulmx_colrow {T : ringType } p q (A : 'M[T]_(p,q)) (B : 'M[T]_(q,p)) : 
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

Local Lemma cn m n : (m <= n)%N -> (m + (n - m) = n)%N.
Proof. by move=>lemn; rewrite addnC subnK. Qed.

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
have P2: (m + (n - m) <= n)%N by rewrite (cn (unitary_dim UU)).
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
1,2: rewrite linearZl/= (Hi _ P4) PA eq_lshift ?nkj ?mulr0// eqxx mulr1 addr0 
-(inj_eq (@ord_inj _)) (gtn_eqF P4)=>->. by rewrite scale0r.
move: (form1_row_schmidt V (lshift (n - m) i)) (Ur i i).
rewrite P1 P5 !addr0 !linearZl linearZr/= mulrA -normCK !PA !eqxx 
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
  1,2: rewrite linearZl linearZr/= PA ?nkj ?mulr0// ?PA eqxx mulr1 addr0. 
  case: eqP=>[E|/eqP E /eqP]; first by move: ltji; rewrite E ltnn.
  by rewrite mulr0n mulf_eq0 conjC_eq0 sqrtC_eq0 -[D 0 j == 0]negbK P5// 
    1 ?leq_eqVlt ?ltji ?orbT// ?orbF =>/eqP.
have P9: row i A = u_ i 0 0 *: row i (schmidt A).
  rewrite P6 (bigD1 i)//= big1=>[j|]; 
  by rewrite ?addr0// andbC -ltn_neqAle=>/P8->; rewrite scale0r.
have Q2 : `|u_ i 0 0| = sqrtC (D 0 i). move: (P3 i i).
  rewrite P9 linearZl linearZr/= PA !eqxx mulr1 -normCK mulr1n.
  by move/(f_equal sqrtC); rewrite sqrCK.
have Q3 : u_ i 0 0 >= 0.
  by move: (form1_row_schmidt A i); rewrite P9 linearZl/= PA eqxx mulr1.
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
Proof. by rewrite -castrv_qualifier; exact: svd_diag_exd. Qed.

Lemma svd_diag_exdr p q (D: 'rV[R]_(minn p q)) : 
  D \is is_svd_diag -> svd_d_exdr D \is is_svd_diag.
Proof. by rewrite -castrv_qualifier; exact: svd_diag_exd. Qed.

Lemma form_diag_schmidt1 m n (lemn : (m <= n)%N) (A : 'M[R]_(m,n)) (D : 'rV[R]_m): 
  D \is is_svd_diag -> A *m A ^*t = diag_mx D ->
  A = castmx (erefl m, (cn lemn)) (row_mx (diag_mx (sqrtdmx D)) 0) 
      *m schmidt (castmx ((cn lemn),erefl n) (col_mx A 0)).
Proof.
move=> Dd PA; set De := castmx (erefl _, (cn lemn)) (row_mx D 0).
set Ae := castmx ((cn lemn), erefl _) (col_mx A 0).
have PDe : De \is is_svd_diag by rewrite /De -castrv_qualifier svd_diag_exd.
have PAe: Ae *m Ae ^*t = diag_mx De by rewrite /Ae adjmx_cast/= castmx_mul/= 
  /De diagmx_cast; f_equal; rewrite adjmxE tr_col_mx map_row_mx !raddf0/= 
  mul_col_row diag_mx_row PA mulmx0 !mul0mx linear0.
move: (form_diag_schmidt PDe PAe). 
move/(f_equal (castmx (esym (cn lemn), erefl _)))/(f_equal usubmx).
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
        (svdp.2 \is unitarymx) &  (A == svdp.1.1 *m castmx (erefl m, (cn lemn)) 
                              (row_mx (diag_mx (svdp.1.2)) 0) *m svdp.2 ^*t)]).
Proof.
move: (psdmx_svd (form_psd A))=>[sdpsd]; set U0 := sdpsd.1; set D0 := sdpsd.2.
move=>/and3P [U0U D0SD /eqP P1].
have: (U0 *m A) *m (U0 *m A)^*t = diag_mx D0 
  by rewrite adjmxM mulmxA mulmxUC// -mulmxA mulUmx// mulmxA.
move/(form_diag_schmidt1 lemn D0SD); rewrite mulUmx// mulmxA=>P2.
exists ((U0^*t,(sqrtdmx D0)), 
  (schmidt (castmx ((cn lemn), erefl n) (col_mx (U0 *m A) 0)))^*t).
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
apply/and4P; split=>//; first by rewrite -castrv_qualifier.
by rewrite -(adjmxK A) P4 !adjmxM adjmxK cdiag_adjmx svd_diag_conj// mulmxA.
move: (svd_subproof_lemn lemn A)=>[[[U D] V] /=/and4P[P1 P2 P3 /eqP P4]].
have E1: (m = minn m n) by apply/esym/minn_idPl.
set D' := castmx (erefl _, E1) D.
exists ((U,D'),V); apply/and4P; split=>//=; first by rewrite -castrv_qualifier.
apply/eqP; rewrite P4; do 2 f_equal; rewrite /cdiag_mx block_mx_castc0; 
  do 2 apply/(canLR (castmxKV _ _))=>/=; rewrite !castmx_comp/= etrans_erefl /D'.
have E4: (m - n = 0)%N by move: {+}lemn=>/eqP.
move: (etrans (min_idl m n) (esym (addn0 m)))=>E2.
move: (etrans (min_idr m n) (esym (cn lemn)))=>E3.
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
Proof. by rewrite /svds_d -castrv_qualifier svd_d_svd_diag. Qed.

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
move=>UU DA; have /unitarymx_spectralP P: A \is normalmx. apply/normalmxP. 
rewrite -DA -adjmxE !adjmxM !mulmxA adjmxK mulmxtVK// [in RHS]mulmxtVK//.
by f_equal; rewrite -!mulmxA; f_equal; rewrite diag_mx_adj diag_mxC.
move: DA; rewrite {1}P=>/(f_equal char_poly). 
by rewrite !char_poly_dec// ?spectral_unitarymx// =>/poly_unique_sort.
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
rewrite -Ps2=>/(f_equal (col_perm (fingroup.invg s2))).
rewrite -!col_permM fingroup.mulVg col_perm1=>P1.
have: col_perm (fingroup.mulg (fingroup.invg s2) s1) (svd_d_exdl v .^+ 2) 
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
have Dv': v' \is is_svd_diag by rewrite /v' -castrv_qualifier.
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
  *m (svd_u A)^*t by rewrite -(svd_d_unique _ _ _ P1)// -?castrv_qualifier svd_pE.
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
    ?trmx_unitary// ?trmxC_unitary// -?castrv_qualifier svd_pE.
by rewrite {1}(svdE A) !trmx_mul !adjmxK cdiag_trmx mulmxA.
Qed.

Lemma svds_d_trmx n (A: 'M[R]_n) : svds_d (A^T) = svds_d A.
Proof. by rewrite /svds_d svd_d_trmx 
(eq_irrelevance (minnC n n) (erefl (minn n n))) castmx_id. Qed.


Lemma svd_d_conjmx m n (A:'M[R]_(m,n)) : 
  svd_d (A^*m) = (svd_d A).
Proof. 
by rewrite -[in LHS](trmxK A) -adjmxEr svd_d_adjmx svd_d_trmx castmx_comp castmx_id.
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
  (schmidt (castmx (cn P1, erefl n) (col_mx U 0)))^*t^*t.
rewrite (svd_d_unique _ _ _ P2)// ?unitarymx1// ?const_svd_diag//.
rewrite trmxC_unitary; by apply schmidt_unitarymx.
rewrite adjmxK mul1mx; move: {+}UU=>/unitarymxP; rewrite -diag_const_mx=>P2.
rewrite {1}(@form_diag_schmidt1 _ _ P1 U _ _ P2) ?const_svd_diag//; f_equal.
rewrite /cdiag_mx block_mx_castc0 castmx_comp/= etrans_id.
move: (min_idl m n) (min_idr m n) (cn P1)=>P3 P4 P5.
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
  *m (1%:M)^*t by rewrite (svd_d_unique _ _ _ P1)// ?unitarymx1// -castrv_qualifier. 
by rewrite mul1mx adjmx_const conjC1 mulmx1 cdiag_mx_diag castmx_comp/= castmx_id.
Qed.

Lemma svds_diagmx n (D : 'rV[R]_n) : D \is is_svd_diag -> svds_d (diag_mx D) = D.
Proof. by rewrite /svds_d=>/svd_diagmx->; rewrite castmx_comp castmx_id. Qed.

End SingularValueDecomposition.

Section Induced2Norm.
Variable (R: numClosedFieldType).

Lemma bigmax_find (d : unit) (T : orderType d) (I : finType) i0 (P : pred I) 
  (F : I -> T) x: P i0 -> (x <= F i0)%O -> (forall i, P i -> F i <= F i0)%O ->
  (\big[Order.max/x]_(i | P i) F i)%O = F i0.
Proof.
by move=>P1 P2 P3; apply/eqP; rewrite eq_le; apply/andP; split;
[apply/bigmax_lerP | apply ler_bigmax_cond].
Qed.
Arguments bigmax_find {d T I} i0 {P F x}.

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
move=>P1; have P2 i : D 0 i >= 0 by move/svd_diag_nneg/nnegmxP: P1=>/(_ 0 i).
have ->: \big[maxr/0%:R]_i (D 0 i) = (\big[maxr/0%:nng]_i (@NngNum R (D 0 i) 
  (P2 i)))%:nngnum by elim/big_ind2 : _ => //= a a' b b' ->{a'} ->{b'}; 
  case: (leP a b) => ab; [rewrite max_r | rewrite max_l // ltW].
rewrite (bigmax_find c0)// -?num_le/= ?P2// =>i _.
by rewrite -num_le/=; move/svd_diag_decreasing/is_decreasingP: P1=>/(_ c0 i)/=.
Qed.

Definition i2norm m n (M : 'M[R]_(m,n)) := \big[maxr/0%:R]_i (svd_d M 0 i).

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
case: m A=>[A _|m]; last case: n=>[A _|n A]. 1,2: by rewrite mx_dim0.
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
Proof. by rewrite qualifE i2norm_ge0. Qed.

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
rewrite -(ler_pexpn2r (ltn0Sn 1)) ?nnegrE ?mulr_ge0 ?normv_ge0// exprMn 
  -!dot_l2norm /mxtrace mulr_sumr; apply ler_sum=> i _.
rewrite !dot_dotmxE row_diag_mul linearZl linearZr/= mulrA.
apply ler_pmul=>//; rewrite -?normCK ?exprn_ge0// ?dnorm_ge0// 
  (ler_pexpn2r (ltn0Sn 1)) ?nnegrE// ger0_norm ?svd_diag_ge0//.
by move/svd_diag_decreasing/is_decreasingP: P1=>/(_ 0 i)/=.
Qed.

Lemma l2norm_cdiag_mul m n p (D: 'rV[R]_(minn m.+1 n.+1)) 
  (M : 'M[R]_(n.+1,p)) : D \is is_svd_diag ->
  l2norm (cdiag_mx D *m M) <= D 0 c0 * l2norm M.
Proof.
move=>P1; move: {+}P1=>/is_svd_diagP/(_ c0) [P2 _].
rewrite -(ler_pexpn2r (ltn0Sn 1)) ?nnegrE ?mulr_ge0 ?normv_ge0// exprMn 
  -!dot_l2norm adjmxM mulmxA mxtrace_mulC !mulmxA cdiag_mx_mulr -diag_mx_dmul
  svd_d_exdr_conj -diag_mx_adj mxtrace_mulC -mulmxA mulmxA -adjmxM mxtrace_mulC 
  /mxtrace mulr_sumr; apply ler_sum=> i _.
rewrite !dot_dotmxE row_diag_mul linearZl linearZr/= mulrA.
apply ler_pmul=>//; rewrite -?normCK ?exprn_ge0// ?dnorm_ge0// (ler_pexpn2r 
  (ltn0Sn 1)) ?nnegrE// ger0_norm ?svd_diag_ge0//; first by apply/svd_diag_exdr.
rewrite /svd_d_exdr castmxE ord1/=; set j := (cast_ord (esym (min_idr m.+1 n.+1)) i).
rewrite -(splitK j) mxE/=; case: (fintype.split (unsplit (fintype.split j)))=>a/=.
by move/svd_diag_decreasing/is_decreasingP: P1=>/(_ c0 a)/=. by rewrite mxE.
Qed.

Lemma i2norm_dotr m n p (M : 'M[R]_(m,n)) (N : 'M[R]_(n,p)): 
  l2norm (M *m N) <= i2norm M * l2norm N.
Proof.
case: n M N=>[M N|n]; last case: m=>[M N|m]; last case: p=>[M N|p M N].
1,2,3: by rewrite !mx_dim0 ?mulmx0 ?normv0 ?i2norm0 ?mul0r// mulr0.
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
by apply ler_add; apply (le_trans (i2norm_dotr _ _)); rewrite P1 mulr1.
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
case: m A=>[A|m]; last case: n =>[A|n A]. 1,2: by rewrite !mx_dim0 i2norm0 normv0.
rewrite i2norm_Sn {2}(svdE A) l2normUr ?trmxC_unitary ?svd_pE// l2normUl ?svd_pE//.
rewrite l2norm_dotV cdiag_mx_mulr -diag_mx_dmul svd_d_exdr_conj -diag_mx_adj -l2norm_dotV.
rewrite l2norm_diag -(ler_pexpn2r (ltn0Sn 1)) ?nnegrE ?svd_d_ge0// ?normv_ge0//.
rewrite -svd_d_exdr0 /l2norm sqrtCK (bigD1 (0,0))//= ger0_norm.
apply/nnegmxP/svd_diag_nneg/svd_diag_exdr/svd_d_svd_diag.
apply ler_paddr=>//. apply sumr_ge0=>i _. rewrite exprn_ge0//.
Qed.

Lemma i2normM m n p (A : 'M[R]_(m,n)) (B : 'M[R]_(n,p)) : 
  i2norm (A *m B) <= i2norm A * i2norm B.
Proof.
case: m A=>[A|m]; last case: p B=>[B A|p]; last case: n=>[B A|n B A].
1,2,3: by rewrite !mx_dim0 ?mulmx0 !i2norm0 ?mul0r ?mulr0.
move: (i2norm_existsr (A *m B) n)=>[C P1 <-].
rewrite -mulmxA. apply (le_trans (i2norm_dotr _ _)).
apply ler_pmul=>//. apply i2norm_ge0. apply normv_ge0.
by apply (le_trans (i2norm_dotr _ _)); rewrite P1 mulr1.
Qed.

Lemma i2norm_elem m n (A : 'M[R]_(m,n)) : forall i j, `|A i j| <= i2norm A.
Proof.
move=>i j. suff ->: `|A i j| = l2norm ((delta_mx i i) *m A *m (delta_mx j j)).
apply (le_trans (i2norm_dotr _ _)). rewrite l2norm_deltamx mulr1.
apply (le_trans (i2normM _ _)). apply ler_pimull. apply i2norm_ge0.
apply (le_trans (i2norm_l2norm _)). by rewrite l2norm_deltamx.
rewrite /l2norm /pnorm (bigD1 (i,j))//= big1=>[d /pair_neq[P1|P1]|].
1: rewrite -mulmxA. 1,2: by rewrite !mxE big1 ?normr0 ?expr0n// =>k _; 
   rewrite !mxE P1/= ?andbF ?mulr0 ?mul0r.
rewrite mxE (bigD1 j)//= big1=>[k /negPf nkj|]; rewrite !mxE ?nkj/= ?mulr0// 
  (bigD1 i)//= big1=>[k /negPf nkj|]; rewrite !mxE ?nkj/= ?andbF ?mul0r//; 
  rewrite !eqxx/= !addr0 mulr1 mul1r sqrCK//.
Qed.

Canonical i2norm_vnorm m n := 
  Vnorm (@i2norm_triangle m n) (@i2norm0_eq0 m n) (@i2normZ m n).

End Induced2Norm.

Section SchattenNorm.
Variable (R: numClosedFieldType) (p : nat).

Definition schattennorm m n (M : 'M[R]_(m,n)) := (pnorm p (svd_d M)).

Lemma schattennorm_exdr m n (M : 'M[R]_(m,n)) : 
  schattennorm M = (pnorm p (svd_d_exdr (svd_d M))).
Proof.
rewrite /schattennorm !pnorm_pair !big_ord1. f_equal.
apply (@svd_d_exd_sumr _ _ _ (svd_d M) (fun x=>`|x|^+p.+1)).
by rewrite normr0 expr0n.
Qed.

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
Proof. by rewrite -schattennorm_trmx -adjmxEl schattennorm_adjmx. Qed.

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

End fbtrnorm_inherited.

Section FrobeniusNorm.
Variable (R: numClosedFieldType).

Lemma fbnorm_dotr m n p (M : 'M[R]_(m,n)) (N : 'M[R]_(n,p)): 
  l2norm (M *m N) <= fbnorm M * i2norm N.
Proof.
case: m M=>[M|m M]; last case: p N=>[N|p N]; last case: n M N=>[M N|n M N].
1,2,3: by rewrite !mx_dim0 ?mulmx0 ?normv0 ?fbnorm0 ?mul0r// mulr0.
apply (le_trans (i2norm_dotl _ _)).
by rewrite mulrC ler_pmul// ?normv_ge0// /fbnorm {1}(svdE M) 
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
Proof.
case: n x y=>[x y|n x y]; last case: m x y=>[x y|m x y].
1,2: by rewrite !mx_dim0 !fbnorm0 addr0.
move: (fbnorm_existsr (x+y))=>[A P1 <-].
rewrite mulmxDl. apply (le_trans (l2norm_triangle _ _)).
by apply ler_add; apply (le_trans (fbnorm_dotr _ _)); rewrite P1 mulr1.
Qed.

Lemma fbnormM m n p (x : 'M[R]_(m,n)) (y: 'M[R]_(n,p)) : 
  fbnorm (x *m y) <= fbnorm x * i2norm y.
Proof.
case: m x y=>[x y|m]; last case: p=>[x y|p]; last case: n=>[x y|n x y].
1,2,3: by rewrite !mx_dim0 ?mulmx0 ?i2norm0 ?fbnorm0 ?mulr0// mul0r.
move: (fbnorm_existsr (x*m y))=>[A PA <-].
rewrite -mulmxA. apply (le_trans (fbnorm_dotr _ _)).
apply ler_pmul=>//. apply schattennorm_ge0. apply i2norm_ge0.
by apply (le_trans (i2normM _ _)); rewrite PA mulr1.
Qed.

Lemma i2norm_fbnorm m n (M : 'M[R]_(m,n)) : i2norm M <= fbnorm M.
Proof.
case: m M=>[M|m]; last case: n=>[M|n M]. 1,2: by rewrite !mx_dim0 i2norm0 fbnorm0.
rewrite -(ler_pexpn2r (ltn0Sn 1)) ?nnegrE ?i2norm_ge0// ?schattennorm_ge0//.
rewrite i2norm_Sn /fbnorm /schattennorm pnorm_pair big_ord1 sqrtCK (bigD1 (c0 _ _))//= 
  ger0_norm ?svd_d_ge0// ler_paddr=>//. apply sumr_ge0=>i _. rewrite exprn_ge0//.
Qed.

Canonical fbnorm_vnorm m n := 
  Vnorm (@fbnorm_triangle m n) (@fbnorm0_eq0 _ m n) (@fbnormZ _ m n).

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
Proof. by rewrite /i1fun mulmxDr linearD/= ler_norm_add. Qed.

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
apply ler_sum=>i _; rewrite normrM mulrC ler_pmul=>//.
by apply (le_trans (i2norm_elem _ _ _)); rewrite i2normUr ?svd_pE// i2normUl 
  ?trmxC_unitary ?svd_pE// i2norm_adjmx. by rewrite ger0_norm// svd_d_ge0.
by rewrite -mulr_sumr mulrC trnorm_svdE.
Qed.

Lemma trnorm_existsr m n (M: 'M[R]_(m.+1,n.+1)) : exists2 A : 'M[R]_(m.+1,n.+1),
  (i2norm A = 1) & (i1fun A M = trnorm M).
Proof.
exists (svd_u M *m cdiag_mx (const_mx 1) *m (svd_v M)^*t).
rewrite i2normUr ?trmxC_unitary ?i2normUl ?svd_pE// i2norm_Sn svd_cdiagmx.
by apply/const_svd_diag. by rewrite mxE.
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
1,2: by rewrite !mx_dim0 !trnorm0 addr0.
move: (trnorm_existsr (x+y))=>[A P1 <-].
apply (le_trans (i1fun_triangle _ _ _ )). 
by apply ler_add; apply (le_trans (trnorm_i1funr _ _)); rewrite P1 mulr1.
Qed.

Lemma trnormM m n p (x : 'M[R]_(m,n)) (y : 'M[R]_(n,p)) : 
  trnorm (x *m y) <= trnorm x * i2norm y.
Proof.
case: m x y=>[x y|m]; last case: p=>[x y|p]; last case: n=>[x y|n x y].
1,2,3: by rewrite !mx_dim0 ?mulmx0 ?i2norm0 ?trnorm0 ?mulr0// mul0r.
move: (trnorm_existsr (x*m y))=>[A PA <-].
rewrite i1funA. apply (le_trans (trnorm_i1funr _ _)).
apply ler_pmul=>//. apply trnorm_ge0. apply i2norm_ge0.
by apply (le_trans (i2normM _ _)); rewrite PA mul1r i2norm_adjmx.
Qed.

Lemma i2norm_trnorm m n (M : 'M[R]_(m,n)) : i2norm M <= trnorm M.
Proof.
case: m M=>[M|m]; last case: n=>[M|n M]. 1,2: by rewrite !mx_dim0 i2norm0 trnorm0.
rewrite i2norm_Sn trnorm_svdE (bigD1 (c0 _ _))//=. rewrite ler_addl.
apply sumr_ge0=>i _. apply svd_d_ge0.
Qed.

Lemma trnorm_ge_tr n (M : 'M[R]_n) : `| \tr M | <= trnorm M.
Proof.
rewrite {1}(svdE M) mxtrace_mulC mulmxA tr_mul_diag trnorm_svdE.
apply: (le_trans (ler_norm_sum _ _ _)).
apply ler_sum=>i _. rewrite normrM [X in X * _]ger0_norm ?svd_d_ge0//.
apply ler_pimulr. apply svd_d_ge0. 
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

Lemma trnorm_inner n p (M : 'M[R]_n) (N : 'M[R]_(p,n)) : 
  `| \tr (N *m M *m N^*t ) | <= \tr| M | * \tr(N *m N^*t ).
Proof.
rewrite mxtrace_mulC mulmxA mxtrace_mulC.
apply (le_trans (trnorm_ge_tr _)).
apply (le_trans (trnormM _ _)).
apply ler_pmul=>//. apply schattennorm_ge0. apply i2norm_ge0.
apply (le_trans (i2norm_trnorm _)).
by rewrite [X in _ <= X]mxtrace_mulC psdmx_trnorm// formV_psd.
Qed.

Lemma form_tr_ge0 n m (A : 'M[R]_(m,n)) : 0 <= \tr (A *m A^*t ).
Proof. by rewrite dot_l2norm exprn_ge0// pnorm_ge0. Qed.

Lemma form_tr_eq0 n m (A : 'M[R]_(m,n)) : \tr (A *m A^*t ) = 0 -> A = 0.
Proof. by move/eqP; rewrite dot_l2norm sqrf_eq0=>/eqP; apply pnorm0_eq0. Qed.

Canonical trnorm_vnorm m n := 
  Vnorm (@trnorm_triangle m n) (@trnorm0_eq0 _ m n) (@trnormZ _ m n).

End TraceNorm.

(****************************************************************************)
(* lowner order over 'M[R]_n as partial order, A <= B iff B - A \is psdmx   *)
(****************************************************************************)
Section LownerPOrder.
Variable (R: realType).
Local Notation C := R[i].
Local Open Scope ring_scope.
Definition lownerle n (M N : 'M[C]_n) := (N - M) \is psdmx.
Definition lownerlt n (M N : 'M[C]_n) := (N != M) && (lownerle M N).

Lemma lownerlt_def n (x y : 'M[C]_n): lownerlt x y = (y != x) && (lownerle x y).
Proof. by rewrite /lownerlt. Qed.

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

Definition lowner_porderMixin n := LePOrderMixin 
  (@lownerlt_def n) (@lownerle_refl n) (@lownerle_anti n) (@lownerle_trans n).
(* Fact vorder_display : unit. Proof. exact: tt. Qed. *)
(* why using vorder_display fails to use <=? *)
Canonical lowner_porderType n := 
  POrderType vorder_display 'M[C]_n (@lowner_porderMixin n).

Definition denmx_lporderMixin n := [porderMixin of 'MDen[C]_n by <:].
Canonical denmx_lporderType n :=
  Eval hnf in POrderType vorder_display 'MDen[C]_n (@denmx_lporderMixin n).

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

Import VOrder.Exports.
Definition lowner_vorderMixin n := VOrderMixin (@lemx_add2rP n) (@lemx_pscale2lP n).
Canonical lowner_vorderType n := VOrderType C 'M[C]_n (@lowner_vorderMixin n).

Lemma pscalemx_lge0 n (x : 'M[C]_n) (a : C) : 
  (0 : 'M[C]_n) ⊏ x -> (0 : 'M[C]_n) ⊑ a *: x = (0 <= a).
Proof.
move=>xgt0. apply/Bool.eq_iff_eq_true; split; last first.
by move=>age0; apply: scalev_ge0=>//; apply/ltW.
move: xgt0. rewrite lt_def {1 2}/Order.le/= /lownerle !subr0=>/andP[nx0 px] /psdmx_trnorm pz.
move: (trnorm_ge0 (a *: x)). rewrite pz linearZ/= pmulr_lge0//.
by rewrite lt_def -!psdmx_trnorm// trnorm_eq0 trnorm_ge0 nx0.
Qed.

Import CanVOrder.Exports.
Definition lowner_canVOrderMixin n := CanVOrderMixin (@pscalemx_lge0 n).
Canonical lowner_canVOrderType n := CanVOrderType C 'M[C]_n (@lowner_canVOrderMixin n).

(* Check @closed [topologicalType of 'M[C]_n]. *) 
Import CTopology.Exports.
Local Open Scope classical_set_scope.
Local Open Scope complex_scope.

Lemma form_nng_neq0 n x : reflect (exists u: 'rV[C]_n, 
  (0 < \tr (u *m u^*t)) && (\tr (u *m x *m u^*t) \isn't Num.nneg))
  (~~ ((0 : 'M[C]_n) ⊑ x)).
apply (iffP negP). apply contra_notP.
rewrite -forallNP=>P1. rewrite le_lownerE subr0. apply/psdmx_dot=>u.
move: (P1 u). move/negP. rewrite negb_and=>/orP[|].
rewrite lt_def form_tr_ge0 negb_and/= orbF negbK=>/eqP/form_tr_eq0->.
by rewrite !mul0mx linear0 nnegrE.
by rewrite negbK.
apply contraPnot. rewrite -forallNP le_lownerE subr0=>/psdmx_dot=>P1 u.
by apply/negP; rewrite negb_and negbK P1 orbT.
Qed.

Lemma Cnng_open (t : C) : t \isn't Num.nneg -> 
  exists2 e, 0 < e & forall s, `|s - t| < e -> s \isn't Num.nneg.
rewrite nnegrE lecE/= negb_and -real_ltNge ?real0// ?num_real// =>/orP[P1|P1].
exists (`|Im t|)%:C=>[|s]; first by rewrite ltcR normr_gt0.
2: exists (`|Re t|)%:C=>[|s]; first by move: P1; rewrite ltcR !lt_def 
  normr_ge0 normr_eq0 eq_sym=>/andP[->].
all: rewrite nnegrE lecE negb_and/= -normr_gt0=>P2.
move: (le_lt_trans (normc_ge_Im _) P2). 2: move: (le_lt_trans (normc_ge_Re _) P2).
all: rewrite ltcR raddfB/= -normrN opprB =>P3.
move: (le_lt_trans (ler_sub_dist _ _) P3).
by rewrite ltr_subl_addl -ltr_subl_addr addrN=>->.
move/ltr_distlC_addr: P3. 
by rewrite ltr0_norm// addrN -real_ltNge ?real0// ?num_real// orbC=>->.
Qed.

Lemma psdmx_closed n : (closed [set x : 'M[C]_n | (0 : 'M[C]_n) ⊑ x])%classic.
Proof.
case: n=>[x/= _|n]; first by rewrite !mx_dim0. 
rewrite (_ : mkset _ = ~` [set x | ~ (0 : 'M[C]_n.+1) ⊑ x]).
by rewrite predeqE=>x /=; rewrite notK.
rewrite closedC. move=> x /= /negP /form_nng_neq0 [u /andP[P1 /Cnng_open [e egt0 Pe]]].
move: (@cmxnorm_ubounded R n n (trnorm_vnorm _ _ _)) =>[c cgt0 Pc]; rewrite nbhs_ballP. 
exists (e/c/(\tr (u *m u ^*t)))=>/=[|y/=]; first by do 2 apply divr_gt0=>//.
rewrite -ball_normE/==>Pb; apply/negP/form_nng_neq0.
exists u; apply/andP; split=>//; apply Pe.
rewrite /ball/= -linearB/= -mulmxBl -mulmxBr.
apply: (le_lt_trans (trnorm_inner _ _)).
rewrite mulrC -lter_pdivl_mull// mulrC; apply: (le_lt_trans (Pc _)).
by rewrite -lter_pdivl_mull// mulrA [_ * e]mulrC -opprB normrN.
Qed.

Lemma trnorm_add_eq n (x y : 'M[C]_n) : (0 : 'M[C]_n) ⊑ x -> (0 : 'M[C]_n) ⊑ y 
  -> trnorm x  + trnorm y = trnorm (x + y).
Proof.
rewrite !le_lownerE !subr0=>P1 P2. move: (psdmx_add P1 P2).
move: P1 P2=>/psdmx_trnorm->/psdmx_trnorm->/psdmx_trnorm->.
by rewrite linearD.
Qed.

Import CmxNormCvg.
Canonical trnorm_mxnormcvg n := @Cmxnormcvg _ _ _ _ _ (trnorm_vnorm _ _ _) 
  (@lemx_add2rP n) (@lemx_pscale2lP n) (@psdmx_closed n).

(* restate the cmxcvg of lowner order and trnorm *)
Lemma cmxcvg_trnorm m n (u : nat -> 'M[C]_(m,n)) (a : 'M[C]_(m,n)) : 
  u --> a -> ((@trnorm _ _ _) \o u) --> \tr| a |.
Proof. by apply/cmxcvg_normv. Qed.

Lemma is_cmxcvg_trnorm m n (u : nat -> 'M[C]_(m,n)) : 
  cvg u -> cvg ((@trnorm _ _ _) \o u).
Proof. by apply/is_cmxcvg_normv. Qed.

Lemma cmxlim_trnorm m n (u : nat -> 'M[C]_(m,n)) : 
  cvg u -> lim ((@trnorm _ _ _) \o u) = \tr| lim u |.
Proof. by apply/cmxlim_normv. Qed.

Lemma mxnondecreasing_is_cvg n (f : nat -> 'M[C]_n) (b : 'M[C]_n) :
  nondecreasing_seq f -> ubounded_by b f -> cvg f.
Proof. exact: (cmxnondecreasing_is_cvg (trnorm_mxnormcvg n)). Qed.

Lemma mxnonincreasing_is_cvg n (f : nat -> 'M[C]_n) (b : 'M[C]_n) :
  nonincreasing_seq f -> lbounded_by b f -> cvg f.
Proof. exact: (cmxnonincreasing_is_cvg (trnorm_mxnormcvg n)). Qed.

Lemma closed_gemx n (x : 'M[C]_n) : closed [set y : 'M[C]_n | x ⊑ y ].
Proof. exact: (cmxclosed_ge (trnorm_mxnormcvg n)). Qed.

Lemma closed_lemx n (x : 'M[C]_n) : closed [set y : 'M[C]_n | y ⊑ x ].
Proof. exact: (cmxclosed_le (trnorm_mxnormcvg n)). Qed.

Lemma lim_gemx_near n (x : 'M[C]_n) (u : nat -> 'M[C]_n) : 
  cvg u -> (\forall n \near \oo, x ⊑ u n) -> x ⊑ lim u.
Proof. exact: (cmxlim_ge_near (trnorm_mxnormcvg n)). Qed.

Lemma lim_lemx_near n (x : 'M[C]_n) (u : nat -> 'M[C]_n) : 
  cvg u -> (\forall n \near \oo, u n ⊑ x) -> lim u ⊑ x.
Proof. exact: (cmxlim_le_near (trnorm_mxnormcvg n)). Qed.

Lemma lemx_lim_near n (u_ v_ : nat -> 'M[C]_n) : cvg u_ -> cvg v_ ->
  (\forall n \near \oo, u_ n ⊑ v_ n) -> lim u_ ⊑ lim v_.
Proof. exact: (cmxler_lim_near (trnorm_mxnormcvg n)). Qed.

Lemma lim_gemx n (x : 'M[C]_n) (u : nat -> 'M[C]_n) : 
  cvg u -> lbounded_by x u -> x ⊑ lim u.
Proof. exact: (cmxlim_ge (trnorm_mxnormcvg n)). Qed.

Lemma lim_lemx n (x : 'M[C]_n) (u : nat -> 'M[C]_n) : 
  cvg u -> ubounded_by x u -> lim u ⊑ x.
Proof. exact: (cmxlim_le (trnorm_mxnormcvg n)). Qed.

Lemma lemx_lim n (u v : nat -> 'M[C]_n) : cvg u -> cvg v ->
  (forall n, u n ⊑ v n) -> lim u ⊑ lim v.
Proof. exact: (ler_cmxlim (trnorm_mxnormcvg n)). Qed.

Lemma mxnondecreasing_cvg_le n (u : nat -> 'M[C]_n) :
  nondecreasing_seq u -> cvg u -> ubounded_by (lim u) u.
Proof. exact: (cmxnondecreasing_cvg_le (trnorm_mxnormcvg n)). Qed.

Lemma mxnonincreasing_cvg_ge n (u : nat -> 'M[C]_n) : 
  nonincreasing_seq u -> cvg u -> lbounded_by (lim u) u.
Proof. exact: (cmxnonincreasing_cvg_ge (trnorm_mxnormcvg n)). Qed.

Lemma trace_continuous n : continuous (@mxtrace _ n : 'M[C]_n -> C).
Proof. by apply/cmxscalar_continuous/linearP. Qed.

Lemma closed_letr n (x : C) : closed [set y : 'M[C]_n | \tr y <= x].
Proof. 
rewrite (_ : mkset _ = mxtrace @^-1` [set y | y <= x])%classic.
by apply/funext=>y. apply: cmxcclosed_comp. exact: linearP. apply/cclosed_le.
Qed.

Lemma closed_getr n (x : C) : closed [set y : 'M[C]_n | x <= \tr y].
Proof. 
rewrite (_ : mkset _ = mxtrace @^-1` [set y | x <= y])%classic.
by apply/funext=>y. apply: cmxcclosed_comp. exact: linearP. apply/cclosed_ge.
Qed.

Lemma closed_eqtr n (x : C) : closed [set y : 'M[C]_n | \tr y = x].
Proof. 
rewrite (_ : mkset _ = mxtrace @^-1` [set y | y = x])%classic.
by apply/funext=>y. apply: cmxcclosed_comp. exact: linearP. apply/cclosed_eq.
Qed.

Lemma cmxcvg_trace n (u : nat -> 'M[C]_n) (a : 'M[C]_n) : 
  u --> a -> ((@mxtrace _ n) \o u) --> \tr a.
Proof. by apply/cmxcvg_sfun/linearP. Qed.

Lemma is_cmxcvg_trace n (u : nat -> 'M[C]_n) : cvg u -> cvg ((@mxtrace _ n) \o u).
Proof. by apply/is_cmxcvg_sfun/linearP. Qed.

Lemma cmxlim_trace n (u : nat -> 'M[C]_n) : 
  cvg u -> lim ((@mxtrace _ n) \o u) = \tr (lim u).
Proof. by apply/cmxlim_sfun/linearP. Qed.

End LownerPOrder.

Section DensitymxCPO.
Import CmxNormCvg.
Variable (R: realType).
Local Notation C := R[i].
Local Notation M n := 'M[C]_n.
Local Notation D n := 'MDen[C]_n.

Import CTopology.Exports.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope complex_scope.

Lemma cmxchain_is_cvg n (c : nat -> 'M[C]_n) (mx : 'M[C]_n) : 
  chain c -> (forall i, c i ⊑ mx) -> cvg c.
Proof. 
move/chain_homo; apply: (cmxnondecreasing_is_cvg (@trnorm_mxnormcvg _ _)).
Qed.

Lemma cmxchain_lub n (c : nat -> 'M[C]_n) (mx : 'M[C]_n) : 
  chain c -> (forall i, c i ⊑ mx) -> 
  (forall i, c i ⊑ lim c) /\ (forall x, (forall i, c i ⊑ x) -> lim c ⊑ x).
Proof.
move=>Pc Pu; move: {+}Pc (cmxchain_is_cvg Pc Pu)=>/chain_homo; split=>[|x].
apply: (cmxnondecreasing_cvg_le (@trnorm_mxnormcvg _ _))=>//.
apply: (cmxlim_le (@trnorm_mxnormcvg _ _))=>//.
Qed.

Definition D2M n (x : D n) := x : M n.

Lemma denmx0 n : (0 : 'M[C]_n) \is denmx.
Proof. by apply/denmxP; split; [apply psdmx0 | rewrite linear0 lter01]. Qed.

Definition Denmx0 n := ((DenMx (denmx0 n)) : D n).
Arguments Denmx0 {n}.

Lemma denmx_dim0 : all_equal_to (@Denmx0 0).
Proof. move=>x. apply/val_inj=>/=. apply mx_dim0. Qed.

Definition Dlub n (u : nat -> D n) :=
  if (n == 0)%N then Denmx0 else 
  match lim (@D2M n \o u) \is denmx =P true with
  | ReflectT isden => (DenMx isden : D n)
  | _ => Denmx0
  end.

Lemma leD2M n (x y : D n) : x ⊑ y <-> (x : M n) ⊑ (y : M n).
destruct x. destruct y. by rewrite {1}/@Order.le/= /Order.CanMixin.le/=.
Qed.

Lemma Dge0 n : forall (x : D n), Denmx0 ⊑ x.
Proof.
move=>x. apply/leD2M. destruct x.
rewrite /=le_lownerE subr0. by apply denmx_psd.
Qed.

Lemma Dge0M n : forall x : D n, (0: M n) ⊑ (x : M n).
Proof. by move=>x; move: (Dge0 x); rewrite leD2M. Qed.

Lemma DleI n : forall x : D n, (x : M n) ⊑ 1%:M.
Proof.
move=>x; destruct x; rewrite /=le_lownerE. 
by move: i=>/denmx_obs; rewrite obsmx_psd_eq=>/andP[_].
Qed.

Lemma mxtraceD2M n (a : D n) : \tr a = \tr (a : M n).
Proof. by destruct a. Qed.

Lemma Dtrace_le1 n (a : D n) : \tr a <= 1.
Proof. by destruct a=>/=; move: i=>/denmxP[_]. Qed.

Lemma chainD2M n (u : nat -> D n) : chain u -> chain (@D2M n \o u).
Proof. move=>P i. rewrite /D2M/=. apply/leD2M/P. Qed.

Lemma chainD_lb n (u : nat -> D n) : forall i, (0:M n) ⊑ (@D2M n \o u) i.
Proof. move=>i; by rewrite /D2M Dge0M. Qed.

Lemma chainD_ub n (u : nat -> D n) : forall i, (@D2M n \o u) i ⊑ 1%:M.
Proof. move=>i; by rewrite DleI. Qed.

Lemma Dlub_lub n : forall c : nat -> D n, chain c -> (forall i, c i ⊑ Dlub c) 
  /\ (forall x, (forall i, c i ⊑ x) -> Dlub c ⊑ x).
Proof.
case: n=>[c _|n c Pc]; first by split=>[i |x _]; rewrite ?denmx_dim0 lexx.
move: {+}Pc (chainD_ub c) (chainD2M Pc)=>/chainD2M P1 P2 /chain_homo Pmono.
move: (cmxchain_is_cvg P1 P2) (cmxchain_lub P1 P2)=>Pcvg [Pu Pl].
rewrite /Dlub/=; case: eqP=>P3.
split=>[i|x P4]; first by apply/leD2M=>/=; apply Pu.
  by rewrite leD2M/=; apply Pl.
exfalso; apply P3; apply/denmxP; split.
rewrite -(subr0 (lim (@D2M n.+1 \o c))) -le_lownerE.
apply/(cmxlim_ge (@trnorm_mxnormcvg _ _) Pcvg)/chainD_lb.
rewrite -cmxlim_trace//;  apply/clim_le=>[|j]; first by apply/is_cmxcvg_trace.
rewrite /= /D2M -mxtraceD2M; apply Dtrace_le1.
Qed.

Lemma Dlub_ub n : forall c : nat -> D n, chain c -> (forall i, c i ⊑ Dlub c).
Proof. by move=>c /Dlub_lub=>[[P1]]. Qed.

Lemma Dlub_least n : 
  forall c : nat -> D n, chain c -> forall x, (forall i, c i ⊑ x) -> Dlub c ⊑ x.
Proof. by move=>c /Dlub_lub=>[[_ ]]. Qed.

Import CpoMixin.Exports.
Definition denmx_cpoMixin n := CpoMixin (@Dge0 n) (@Dlub_ub n) (@Dlub_least n).
Canonical denmx_cpoType n := CpoType (D n) (@denmx_cpoMixin n).

End DensitymxCPO.
