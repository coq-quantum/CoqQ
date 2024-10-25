(* -------------------------------------------------------------------- *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra perm fingroup.
From mathcomp.analysis Require Import -(notations)forms.
From mathcomp.classical Require Import boolp.
Require Import notation mcaextra mcextra spectral mxpred.

(* -------------------------------------------------------------------- *)
Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

(* -------------------------------------------------------------------- *)
Local Open Scope ring_scope.

Import Order.Theory GRing.Theory Num.Theory Num.Def.


(******************************************************************************)
(*                      Singular Value Decomposition (SVD)                    *)
(******************************************************************************)
(* let A = 'M[R]_(m,n)  R: numClosedFieldType                                 *)
(*        A = svd_u A *m cdiag_mx (svd_d A) *m (svd_v A)^*t                   *)
(*    where :                                                                 *)
(*        svd_u A is a m * m square unitary matrix                            *)
(*        svd_v A is a n * n square unitary matrix                            *)
(*        svd_d A is 1 * (minn m n) row vector, with nonincreasing order of   *)
(*                singular values                                             *)
(*        cdiag_mx gives the m * n matrix with diagonal elements of           *)
(*                1 * (minn m n) row vector, with 0 for extended part, i.e.   *)
(*                index out of minn m n                                       *)
(*----------------------------------------------------------------------------*)
(* let A = 'M[R]_m  R: numClosedFieldType                                     *)
(*        A = svd_u A *m diag_mx (svds_d A) *m (svd_v A)^*t                   *)
(*    where :                                                                 *)
(*        svds_d A is a 1 * m row vector, with nonincreasing order of         *)
(*                singular values                                             *)
(*----------------------------------------------------------------------------*)
(* let A = 'M[R]_(m,n)  R: numClosedFieldType                                 *)
(*        A = csvd_u A *m diag_mx (csvd_d A) *m (csvd_v A)^*t                 *)
(*    compact-svd, given r = \rank A, where :                                 *)
(*        csvd_u A is a m * r matrix with normalized and pairwise orthogonal  *)
(*                 column vectors, i.e., (csvd_u A)^*t is semi-unitary        *)
(*                 matrices, or, (csvd_u A)^*t *m (csvd_u A) = 1%:M           *)
(*        csvd_v A is a n * r matrix, such that (csvd_v A)^*t is              *)
(*                 semi-unitary                                               *)
(*        csvd_d A is a 1 * r row vector with non-zero singular values        *)
(*                 ordered nonincreasingly                                    *)
(*    technically, we allow r if provided \rank A = r instead of using        *)
(*      \rank A directly as dimensions, to avoid unnecessary type casts.      *)
(*----------------------------------------------------------------------------*)
(* let A = 'M[R]_(m,n)  R: numClosedFieldType                                 *)
(*         svd_f A : nat -> C (ordered singular values)                       *)
(******************************************************************************)

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

Lemma normalmx_scale m (a : R) : (a%:M : 'M[R]_m) \is normalmx.
Proof. 
by apply/normalmxP; rewrite -scalemx1 -!(scalemxAr,scalemxAl) -adjmxE
  adjmxZ -!(scalemxAl,scalemxAr) mulmx1 mul1mx.
Qed.

Lemma spectral_diag_scale n (a : R) : spectral_diag (a%:M : 'M[R]_n) = const_mx a.
Proof.
move: (normalmx_scale n a)=>/eigen_dec/esym.
by rewrite mulmxUC// mulUmx// -{3}scalemx1 -scalemxAl mul1mx 
  -scalemxAr unitarymxKV// scalemx1 -{2}diag_const_mx=>/diag_mx_inj.
Qed.

Lemma spectral_diag0 n : spectral_diag (0 : 'M[R]_n) = 0.
Proof. by rewrite -scalemx0 spectral_diag_scale const_mx0. Qed.

Lemma spectral_diag1 n : spectral_diag (1%:M : 'M[R]_n) = const_mx 1.
Proof. exact: spectral_diag_scale. Qed.

Lemma unitarymx1 n : (1%:M : 'M[R]_n) \is unitarymx.
Proof. by apply/unitarymxP; rewrite mul1mx -adjmxE adjmx_scale conjC1. Qed.

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

Section sort_vect.
Variable (R: numFieldType) (n: nat).
Implicit Type (v : 'rV[R]_n).

Definition rv_nonincreasing :=
  [qualify v : 'rV[R]_n | 
    [forall i : 'I_n, 
      [forall j : 'I_n, (i > j)%N || (v 0 i >= v 0 j) ]]].

Lemma rv_nonincreasingP v :
  reflect (forall i j : 'I_n, (i <= j)%N -> (v 0 i >= v 0 j)) 
    (v \is rv_nonincreasing).
Proof.
apply/(iffP forallP)=>[H i j|H i].
by move: (H i)=>/forallP/(_ j); rewrite ltnNge -implybE=>/implyP.
by apply/forallP=>j; rewrite ltnNge -implybE; apply/implyP/H.
Qed.

Definition rv_cmp :=
  [qualify v : 'rV[R]_n | 
    [forall i : 'I_n, [forall j : 'I_n, (v 0 i >=< v 0 j)]]].

Lemma rv_cmpP v :
  reflect (forall i j, v 0 i >=< v 0 j) (v \is rv_cmp).
Proof. by apply/(iffP forallP)=>H i; apply/forallP. Qed.

Notation geR := (fun x y : R => x >= y).

Lemma rv_nonincreasing_is_cmp v : 
  v \is rv_nonincreasing -> v \is rv_cmp.
Proof.
move=>/rv_nonincreasingP P; apply/rv_cmpP=>i j.
have [/P|/ltnW/P] := leqP i j.
by apply/ge_comparable. by apply/le_comparable.
Qed.

Lemma realmx_is_cmp v : v \is a realmx -> v \is rv_cmp.
Proof. by move=>/realmxP P; apply/rv_cmpP=>i j; apply/real_comparable. Qed.

Lemma geR_transitive (P : {pred R}) :
  {in P & &, transitive (fun x : R => <=%R^~ x)}.
Proof. by move=>x y z _ _ _ Px Pz; apply/(le_trans Pz Px). Qed.

Lemma geR_anti (P : {pred R}) :
  {in P &, antisymmetric (fun x : R => <=%R^~ x)}.
Proof. by move=>x y _ _; rewrite -eq_le=>/eqP->. Qed.

Let s v := [tuple of [seq v 0 i | i <- ord_tuple n]].
Let ss v := sort geR (s v).

Lemma size_sort_s v : size (ss v) == n.
Proof. by rewrite size_sort size_tuple. Qed.

Definition tsort_s v := Tuple (size_sort_s v).

Lemma tsort_sE v : tsort_s v = ss v :> seq R.
Proof. by []. Qed.

(* Lemma all_geR_s v : v \is rv_cmp -> all (has_quality O PR) (s v).
Proof.
move=>/realmxP/(_ 0) Pr; apply/(all_tnthP)=>i.
rewrite tnth_map tnth_ord_tuple. by move: (Pr i).
Qed. 

Lemma all_geR_sort_s v : v \is a realmx -> all (has_quality O PR) (ss v).
Proof. by move=>Pr; rewrite all_sort all_geR_s. Qed. *)

Lemma sort_s_sorted v: v \is rv_cmp -> sorted geR (ss v).
Proof.
move=>Pr; apply: (sort_sorted_in (P := fun x => [exists i, x == v 0 i])).
move=>i j; rewrite /in_mem/==>/existsP[k/eqP->]/existsP[l/eqP->].
by move: Pr=>/rv_cmpP/(_ k l); rewrite orbC.
by apply/all_tnthP=>i; apply/existsP; exists i; rewrite tnth_map tnth_ord_tuple.
Qed.

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

Lemma homo_sort_s v (i j : 'I_n) : v \is rv_cmp -> 
  (i <= j)%N -> (tsort_s v)~_i >= (tsort_s v)~_j.
Proof.
move=>Pr; destruct i; destruct j; rewrite /= !(tnth_nth 0)/= =>P1.
apply: (sorted_leq_nth_in (@geR_transitive _) _ _ _ (sort_s_sorted Pr) m m0)=>//.
all: by rewrite inE; move: (size_sort_s v)=>/eqP->. 
Qed.

Lemma sort_v_nonincreasing v : v \is rv_cmp -> 
  forall i j : 'I_n, (i <= j)%N -> (sort_v v 0 i >= sort_v v 0 j).
Proof. by move=>Pr i j; rewrite !mxE; apply/homo_sort_s. Qed.

Lemma sort_exists v : v \is rv_cmp -> 
  exists (s : 'S_n), col_perm s v \is rv_nonincreasing.
Proof.
move: (perm_sort_v v)=>[p Pp]; exists p. 
by rewrite Pp; apply/rv_nonincreasingP; apply sort_v_nonincreasing.
Qed.

Lemma rv_nonincreasing_sorted_s v : v \is rv_nonincreasing -> sorted geR (s v).
Proof.
move=>P1; rewrite sorted_pairwise=>[x y z +P2|]; first by apply (le_trans P2).
apply/(pairwiseP 0)=>i j; rewrite !inE !size_tuple=>Pi Pj ltij.
rewrite !nth_tnth !tnth_map !tnth_ord_tuple.
move/rv_nonincreasingP: P1=>/(_ (Ordinal Pi) (Ordinal Pj));
by apply=>/=; apply/ltnW.
Qed.

Lemma rv_nonincreasing_sorted v : 
  v \is rv_nonincreasing -> sort_v v = v.
Proof.
pose P : {pred R} := fun x => [exists i, x == v 0 i].
have P1 : {in P & &, transitive (fun x : R => <=%R^~ x)}.
  move=>x y z _ _ _ Px Pz; apply/(le_trans Pz Px).
move/rv_nonincreasing_sorted_s/(sorted_sort_in P1)=>P2.
apply/matrixP=>i j; rewrite !ord1 !mxE (tnth_nth 0)/= /ss P2.
  by apply/all_tnthP=>k; apply/existsP; exists k; rewrite tnth_map tnth_ord_tuple.
by rewrite nth_tnth ltn_ordK tnth_map tnth_ord_tuple.
Qed.

Lemma col_perm_perm_s v (p : 'S_n) : perm_eq (s v) (s (col_perm p v)).
Proof.
apply/tuple_permP. exists (invg p). f_equal.
by apply eq_from_tnth=>i; rewrite !tnth_map !tnth_ord_tuple mxE permKV.
Qed.

Lemma col_perm_rv_cmp v (p : 'S_n) : 
  (col_perm p v \is rv_cmp) = (v \is rv_cmp).
Proof.
apply/eqb_iff; split=>/rv_cmpP P; apply/rv_cmpP=>i j.
by move: (P ((p^-1)%g i) ((p^-1)%g j)); rewrite !mxE !permKV.
by rewrite !mxE.
Qed.

Lemma rv_nonincreasing_perm v (p : 'S_n) :
  v \is rv_nonincreasing -> col_perm p v \is rv_nonincreasing -> col_perm p v = v.
Proof.
move=>P2 P3; rewrite -{2}(rv_nonincreasing_sorted P2) -(rv_nonincreasing_sorted P3).
apply/matrixP=>i j; rewrite !mxE !(tnth_nth 0) !tsort_sE; f_equal.
apply/(perm_sort_inP _ _ (@geR_transitive _) (@geR_anti _)).
  move=>x y /tnthP[k ->]/tnthP[l ->].
  rewrite !tnth_map !tnth_ord_tuple orbC.
  by apply/rv_cmpP/rv_nonincreasing_is_cmp.
by rewrite perm_sym col_perm_perm_s. 
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

End sort_vect.

Arguments rv_nonincreasing {R n}.
Arguments rv_cmp {R n}.

(* TODO : move *)
Lemma big_ord_cast [T] [idx : T] [op : T -> T -> T] m m' 
  (eqm : m' = m) (P: pred 'I_m) (F : 'I_m -> T) :
  \big[op/idx]_(i | P i) F i = \big[op/idx]_(i | P (cast_ord eqm i)) F (cast_ord eqm i).
Proof. case: m / eqm P F=>P F. apply eq_big=>[i|i Pi]; by rewrite cast_ord_id. Qed.

Lemma big_split_ord_cast [T : Type] [idx : T] [op : Monoid.law idx] 
  [m n r : nat] [P : pred 'I_r] (eqr : (m + n)%N = r) (F : 'I_r -> T) :
  \big[op/idx]_(i | P i) F i =
  op (\big[op/idx]_(i | P (cast_ord eqr (lshift n i))) F (cast_ord eqr (lshift n i)))
    (\big[op/idx]_(i | P (cast_ord eqr (rshift m i))) F (cast_ord eqr (rshift m i))).
Proof.
by case: r / eqr P F => P F; rewrite big_split_ord; 
  f_equal=>/=; apply eq_big=>i; rewrite cast_ord_id.
Qed.

Section diag_nonincreasing.
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

Definition svd_diag := 
  [qualify v : 'rV[R]_n | (v \is a nnegmx) && (v \is rv_nonincreasing)].

Lemma svd_diag_nonincreasing v : v \is svd_diag -> v \is rv_nonincreasing.
Proof. by move/andP=>[_ ->]. Qed.

Lemma svd_diag_nneg v : v \is svd_diag -> v \is a nnegmx.
Proof. by move/andP=>[->]. Qed.

Lemma svd_diag_real v : v \is svd_diag -> v \is a realmx.
Proof. by move/svd_diag_nneg/nnegmx_real. Qed.

Lemma svd_diag_ge0 v i : v \is svd_diag -> v 0 i >= 0.
Proof. by rewrite -nnegrE; move/svd_diag_nneg/nnegmxP=>/(_ 0 i). Qed.

Lemma svd_diagP v : reflect (forall i : 'I_n, (v 0 i >= 0) 
  /\ forall j : 'I_n, (i <= j)%N -> (v 0 i >= v 0 j))
    (v \is svd_diag).
Proof.
apply/(iffP andP)=>[[Nn De i]|IH]; 
  (split; [apply/nnegmxP=>// i j | apply/rv_nonincreasingP=>// i j]).
by rewrite ord1 nnegrE; move: (IH j)=>[->].
by move: (IH i)=>[_ /(_ j)].
Qed.

Lemma svd_diag_eq0 v i : v \is svd_diag -> v 0 i = 0 -> 
  forall j : 'I_n, (j >= i)%N -> v 0 j = 0.
Proof.
move/svd_diagP=>P1 P2 j ltij; move: (P1 j) (P1 i) =>[Pj _] [_ /(_ j ltij)].
by rewrite P2 =>Pjn; apply/eqP; rewrite eq_le Pj Pjn.
Qed.

Lemma svd_diag_neq0 v i : v \is svd_diag -> v 0 i != 0 -> 
  forall j : 'I_n, (j <= i)%N -> v 0 j != 0.
Proof.
move/svd_diagP=>P1 P2 j ltij; move: (P1 i) (P1 j) =>[Pi _] [_ /(_ i ltij) Pij].
by apply/lt0r_neq0/(lt_le_trans _ Pij); rewrite lt_def P2 Pi.
Qed.

Lemma sqrt_svd_diag p v : v \is svd_diag -> p.-rootdmx v \is svd_diag.
Proof.
move/svd_diagP=>P; apply/svd_diagP=>i/=; rewrite !mxE.
case: p=>[|p]; first by rewrite !root0C; split=>// j; rewrite mxE root0C lexx.
split=>[|j Pij]; first by rewrite rootC_ge0//; move: (P i)=>[->].
by move: (P j) (P i) =>[P3 _] [P1 /(_ j Pij) P2]; rewrite !mxE ler_rootC.
Qed.

Lemma sqr_svd_diag p v : v \is svd_diag -> v.^+p \is svd_diag.
Proof.
move/svd_diagP=>P; apply/svd_diagP=>i/=; rewrite !mxE; case: p=>[|p].
by rewrite !expr0 ler01; split=>// j; rewrite mxE expr0 lexx. 
split=>[|j Pij]; first by apply/exprn_ge0; move: (P i)=>[->].
by move: (P j) (P i) =>[P3 _] [P1 /(_ j Pij) P2]; rewrite !mxE ler_pXn2r.
Qed.

Lemma svd_diag_conj v : v \is svd_diag -> v ^*m = v.
Proof. 
move/svd_diagP=>P; apply/matrixP=>i j.
by rewrite !mxE !ord1 geC0_conj//; move: (P j)=>[->].
Qed.

Lemma svd_diagZ v a : v \is svd_diag -> 0 <= a -> a *: v \is svd_diag.
Proof.
move/svd_diagP=>P1 P2; apply/svd_diagP=>i; split. 
by rewrite !mxE mulr_ge0//; move: (P1 i)=>[->].
by move=>j Pij; move: (P1 i)=>[_ /(_ j Pij) P3]; rewrite !mxE ler_wpM2l.
Qed.

Lemma const_svd_diag a : 0 <= a -> const_mx a \is svd_diag.
Proof.
move=>P1; apply/svd_diagP=>i.
split=>[|j]; by rewrite !mxE// lexx orbT.
Qed.

Lemma descreasing_row_vec v : v \is a nnegmx ->
  exists (s : 'S_n), col_perm s v \is svd_diag.
Proof.
move=>Nn; move: {+}Nn=>/nnegmx_real/realmx_is_cmp/sort_exists=>[[s Ps]].
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

Lemma svd_d_exdl_conj p q (D : 'rV[R]_(minn p q)) :
  svd_d_exdl D^*m = (svd_d_exdl D)^*m.
Proof. by rewrite /svd_d_exdl castmx_funE !conjmxE map_row_mx raddf0. Qed.

Lemma svd_d_exdr_conj p q (D : 'rV[R]_(minn p q)) :
  svd_d_exdr D^*m = (svd_d_exdr D)^*m.
Proof. by rewrite /svd_d_exdr castmx_funE !conjmxE map_row_mx raddf0. Qed.

Lemma svd_d_exd_sumr p q (D: 'rV[R]_(minn p q)) (f: R-> R) :
  f 0 = 0 -> \sum_i f (D 0 i) = \sum_i f (svd_d_exdr D 0 i).
Proof.
move=>P1; rewrite /svd_d_exdr (big_split_ord_cast (min_idr p q))/= 
  [X in _ + X]big1 ?addr0=>[i _|]; last apply eq_bigr=>i _.
all: by rewrite castmxE ord1 cast_ord_comp cast_ord_id ?row_mxEl// row_mxEr mxE.
Qed.

Lemma svd_d_exd_suml p q (D: 'rV[R]_(minn p q)) (f: R-> R) :
  f 0 = 0 -> \sum_i f (D 0 i) = \sum_i f (svd_d_exdl D 0 i).
Proof.
move=>P1; rewrite /svd_d_exdr (big_split_ord_cast (min_idl p q))/= 
  [X in _ + X]big1 ?addr0=>[i _|]; last apply eq_bigr=>i _.
all: by rewrite castmxE ord1 cast_ord_comp cast_ord_id ?row_mxEl// row_mxEr mxE.
Qed.

Lemma svd_d_exdr_dmul p q (u v : 'rV[R]_(minn p q)) :
  svd_d_exdr u .* svd_d_exdr v = svd_d_exdr (u .* v).
Proof.
apply/matrixP=>i j; rewrite /svd_d_exdr !mxE !castmxE/= ord1.
set k := cast_ord _ _; case: (split_ordP k)=>l ->; 
by rewrite ?row_mxEl ?row_mxEr !mxE// mulr0.
Qed.

Lemma svd_d_exdl_dmul p q (u v : 'rV[R]_(minn p q)) :
  svd_d_exdl u .* svd_d_exdl v = svd_d_exdl (u .* v).
Proof.
apply/matrixP=>i j; rewrite /svd_d_exdr !mxE !castmxE/= ord1.
set k := cast_ord _ _; case: (split_ordP k)=>l ->; 
by rewrite ?row_mxEl ?row_mxEr !mxE// mulr0.
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

Lemma cdiag_mx_is_linear p q : linear (@cdiag_mx p q).
Proof. 
by move=>a A B; rewrite /cdiag_mx linearP/= -[RHS]linearP/= 
  scale_block_mx add_block_mx !scaler0 !addr0.
Qed.
HB.instance Definition _ p q :=
  GRing.isLinear.Build R 'rV_(minn p q) 'M_(p, q) *:%R
    (@cdiag_mx p q) (@cdiag_mx_is_linear p q).

End diag_nonincreasing.

Arguments svd_diag {R n}.

(* from spectral decomposition to svd *)
Section SingularValueDecomposition.
Variable (R: numClosedFieldType).
 (* (m n: nat) Hypothesis (lenm : (m <= n)%N). *)

Local Notation "''[' u , v ]" := (dotmx u v) : ring_scope.
Local Notation "''[' u ]" := '[u, u]%R : ring_scope.

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
  [&& (sdpsd.1 \is unitarymx),  (sdpsd.2 \is svd_diag) &
  (M == sdpsd.1^*t *m diag_mx sdpsd.2 *m sdpsd.1)]).
Proof.
move=>/psdmxP [/hermmx_normal/eigen_dec P1 /descreasing_row_vec [s Ps]].
exists (perm_mx s *m (eigenmx M)^*t, col_perm s (spectral_diag M))=>/=.
apply/and3P; split=>//.
  apply/mul_unitarymx; [apply/perm_mx_unitary|rewrite trmxC_unitary//].
by rewrite diag_perm adjmxM !mulmxA !mulmxKtV// ?perm_mx_unitary// adjmxK; apply/eqP.
Qed.

Lemma dot_dotmxE p q r (A : 'M[R]_(p,q)) (B : 'M_(r,q)) i j : 
  (A *m B ^*t) i j = '[ (row i A), (row j B)].
Proof. by rewrite dotmxE !mxE; apply eq_bigr=>k _; rewrite !mxE. Qed.

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
  D \is svd_diag -> A *m A ^*t = diag_mx D ->
  A = diag_mx (sqrtdmx D) *m schmidt A.
Proof.
move=>P1 P2; have P3 i j : '[ (row i A), (row j A)] = D 0 i *+ (i == j) 
  by rewrite -dot_dotmxE P2 !mxE.
apply/row_matrixP=>i; rewrite row_diag_mul mxE.
move: (schmidt_unitarymx A (leqnn _))=>/row_unitarymxP PA.
elim/ord_ltn_ind: i=> i Hi; move: (P3 i i); rewrite eqxx mulr1n.
case E: (D 0 i == 0); move/eqP: E.
  by move=>->; rewrite sqrtC0 scale0r=>/eqP; rewrite dnorm_eq0=>/eqP.
move/eqP=>P4 Q1; move: (svd_diag_neq0 P1 P4)=>P5.
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
  D \is svd_diag -> row_mx D (0 : 'rV[R]_q) \is svd_diag.
Proof.
move=>P1; apply/svd_diagP=>i; split=>[|j]; first rewrite !mxE. 
by case: (fintype.split i)=>a; [apply/nnegmxP/svd_diag_nneg | rewrite mxE].
rewrite !mxE -{1}(splitK i) -{1}(splitK j); case: (fintype.split i)=>a; 
  case: (fintype.split j)=>b/=; rewrite ?mxE//.
- by apply/rv_nonincreasingP/svd_diag_nonincreasing.
- by move=> _; apply/nnegmxP/svd_diag_nneg.
- by case: b=>b Pb/= Pp; move: (leq_trans Pb (leq_addr a p)); rewrite ltnNge Pp.
Qed.

Lemma svd_diag_exdl p q (D: 'rV[R]_(minn p q)) : 
  D \is svd_diag -> svd_d_exdl D \is svd_diag.
Proof. rewrite castmx_funE; exact: svd_diag_exd. Qed.

Lemma svd_diag_exdr p q (D: 'rV[R]_(minn p q)) : 
  D \is svd_diag -> svd_d_exdr D \is svd_diag.
Proof. by rewrite castmx_funE; exact: svd_diag_exd. Qed.

Lemma form_diag_schmidt1 m n (lemn : (m <= n)%N) (A : 'M[R]_(m,n)) (D : 'rV[R]_m): 
  D \is svd_diag -> A *m A ^*t = diag_mx D ->
  A = castmx (erefl m, (subnKC lemn)) (row_mx (diag_mx (sqrtdmx D)) 0) 
      *m schmidt (castmx ((subnKC lemn),erefl n) (col_mx A 0)).
Proof.
move=> Dd PA; set De := castmx (erefl _, (subnKC lemn)) (row_mx D 0).
set Ae := castmx ((subnKC lemn), erefl _) (col_mx A 0).
have PDe : De \is svd_diag by rewrite /De castmx_funE svd_diag_exd.
have PAe: Ae *m Ae ^*t = diag_mx De by rewrite /Ae castmx_funE/= castmx_mul/= 
  /De diagmx_cast; f_equal; rewrite adjmxE tr_col_mx map_row_mx !raddf0/= 
  mul_col_row diag_mx_row PA mulmx0 !mul0mx linear0.
move: (form_diag_schmidt PDe PAe). 
move/(f_equal (castmx (esym (subnKC lemn), erefl _)))/(f_equal usubmx).
rewrite /Ae {1}esym_erefl castmxK col_mxKu=>{1}->.
rewrite -(castmx_mul (erefl n)) castmx_id -mul_usub_mx; congr (_ *m _).
apply/esym/(canLR (castmxKV _ _))=>/=.
rewrite /De /sqrtdmx /sqrtdmx map_castmx diagmx_cast map_row_mx diag_mx_row.
rewrite castmx_usubmx !castmx_comp /= etrans_erefl etrans_esym castmx_id.
by rewrite col_mxKu.
Qed.

Lemma svd_subproof_lemn m n (lemn : (m <= n)%N) (A : 'M[R]_(m,n)) : 
  (exists svdp : 'M_m * 'rV_m * 'M_n,
    [&& (svdp.1.1 \is unitarymx),  (svdp.1.2 \is svd_diag), 
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
    [&& (svdp.1.1 \is unitarymx),  (svdp.1.2 \is svd_diag), 
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
apply/eqP; rewrite P4; do 2 f_equal; rewrite /cdiag_mx block_mx_castr0; 
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
Lemma svd_u_adj_unitarymx m n (A : 'M[R]_(m,n)) : (svd_u A)^*t \is unitarymx.
Proof. by rewrite adjmx_unitary svd_u_unitarymx. Qed.

Lemma svd_v_unitarymx m n (A : 'M[R]_(m,n)) : svd_v A \is unitarymx.
Proof. by move: (xchooseP (svd_subproof A))=>/and4P[_ _ P1]. Qed.
Lemma svd_v_adj_unitarymx m n (A : 'M[R]_(m,n)) : (svd_v A)^*t \is unitarymx.
Proof. by rewrite adjmx_unitary svd_v_unitarymx. Qed.

Lemma svd_d_svd_diag m n (A : 'M[R]_(m,n)) : svd_d A \is svd_diag.
Proof. by move: (xchooseP (svd_subproof A))=>/and4P[_ P1]. Qed.

Lemma svds_d_svd_diag n (A : 'M[R]_n) : svds_d A \is svd_diag.
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
  U \is unitarymx -> V \is unitarymx -> v \is svd_diag -> 
    A = U *m cdiag_mx v *m V ^*t -> v = svd_d A.
Proof.
move=>UU UV Dv DA; move: (svd_d_spectral_perm A) (svd_diag_exdl Dv) 
  (svd_diag_exdl (svd_d_svd_diag A))=>[s2 Ps2 Dve Dde].
suff: U^*t^*t *m diag_mx (svd_d_exdl v .^+ 2) *m U^*t = A *m A^*t.
move/spectral_unique; rewrite trmxC_unitary=>/(_ UU)[s1].
rewrite -Ps2=>/(f_equal (col_perm (invg s2))).
rewrite -!col_permM fingroup.mulVg col_perm1=>P1.
have: col_perm (mulg (invg s2) s1) (svd_d_exdl v .^+ 2) = (svd_d_exdl v .^+ 2) 
  by apply/rv_nonincreasing_perm; rewrite ?P1; apply/svd_diag_nonincreasing/sqr_svd_diag.
by rewrite P1=>/(dexprm_inj (ltn0Sn 1) (svd_diag_nneg Dde) 
  (svd_diag_nneg Dve))/svd_d_exdl_inj->.
rewrite DA !adjmxM !mulmxA !adjmxK mulmxKtV//.
f_equal; rewrite -mulmxA; f_equal.
by rewrite cdiag_mx_mull svd_diag_conj// dexpmx2.
Qed.

Lemma svds_d_unique n (U V A : 'M[R]_n) (v : 'rV[R]_n) :
  U \is unitarymx -> V \is unitarymx -> v \is svd_diag -> 
    A = U *m diag_mx v *m V ^*t -> v = svds_d A.
Proof.
set v' := (castmx (erefl _, esym (minn_id _)) v).
move: (cdiag_mx_diag v'); rewrite {2}/v' castmxKV=><- PU PV Dv PA.
have Dv': v' \is svd_diag by rewrite /v' castmx_funE.
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

Lemma svds_d_scale n a : svds_d (a%:M : 'M[R]_n) = const_mx `|a|.
move: (svdsE (a%:M : 'M[R]_n))=>P1.
have P2: (a%:M : 'M[R]_n) = ((if a == 0 then 1 else a/`|a|) *: 1%:M) 
  *m diag_mx (const_mx `|a|) *m (1%:M)^*t.
rewrite adjmx_scale conjC1 mulmx1 -scalemxAl mul1mx.
by rewrite -linearZ/= -[LHS]diag_const_mx scalemx_const norm_if_id.
by rewrite (svds_d_unique _ _ _ P2)// ?unitarymxZ ?unitarymx1// 
  ?const_svd_diag// norm_if_norm.
Qed.

Lemma svd_d_scale n a : svd_d (a%:M : 'M[R]_n) = const_mx `|a|.
Proof.
move: (@svds_d_scale n a). rewrite /svds_d=>/esym/castmx_sym->.
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
Proof. by rewrite -scalemx0 svds_d_scale normr0 const_mx0. Qed.

Lemma svds_d1 n : svds_d (1%:M : 'M[R]_n) = const_mx 1.
Proof. by rewrite svds_d_scale normr1. Qed.

Lemma svd_d1 n : svd_d (1%:M : 'M[R]_n) = const_mx 1.
Proof. by rewrite svd_d_scale normr1. Qed.

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
f_equal; rewrite /cdiag_mx block_mx_castr0 castmx_comp/= etrans_id.
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

Lemma svd_d_ge0 m n (A: 'M[R]_(m,n)) i j : 0 <= svd_d A i j.
Proof. by rewrite ord1; apply/svd_diag_ge0/svd_d_svd_diag. Qed.

Lemma svd_d_nneg m n (A: 'M[R]_(m,n)) i j : svd_d A i j \is Num.nneg.
Proof. apply/svd_d_ge0. Qed.

Lemma svds_d_ge0 m (A: 'M[R]_m) i j : 0 <= svds_d A i j.
Proof. by rewrite /svds_d castmxE/= svd_d_ge0. Qed.

Lemma svds_d_nneg m (A: 'M[R]_m) i j : svds_d A i j \is Num.nneg.
Proof. apply/svds_d_ge0. Qed.

Lemma svd_cdiagmx m n (D: 'rV[R]_(minn m n)) : D \is svd_diag -> 
  svd_d (cdiag_mx D) = D.
Proof.
move=>D1; suff P1: (cdiag_mx D) = 1%:M *m (cdiag_mx D) *m (1%:M)^*t.
  by rewrite -(svd_d_unique _ _ _ P1)// ?unitarymx1//. 
by rewrite mul1mx adjmx_scale conjC1 mulmx1.
Qed.

Lemma svd_diagmx n (D : 'rV_n) : D \is svd_diag -> 
  svd_d (diag_mx D) = castmx (erefl _, esym (minn_id _)) D.
Proof.
move=>D1; suff P1: (diag_mx D)= 1%:M *m(cdiag_mx(castmx(erefl _,esym(minn_id n)) D)) 
  *m (1%:M)^*t by rewrite (svd_d_unique _ _ _ P1)// ?unitarymx1// castmx_funE. 
by rewrite mul1mx adjmx_scale conjC1 mulmx1 cdiag_mx_diag castmx_comp/= castmx_id.
Qed.

Lemma svds_diagmx n (D : 'rV_n) : D \is svd_diag -> svds_d (diag_mx D) = D.
Proof. by rewrite /svds_d=>/svd_diagmx->; rewrite castmx_comp castmx_id. Qed.

End SingularValueDecomposition.

#[global] Hint Extern 0 (is_true (svd_u _ \is unitarymx)) => apply: svd_u_unitarymx : core.
#[global] Hint Extern 0 (is_true (svd_v _ \is unitarymx)) => apply: svd_v_unitarymx : core.
#[global] Hint Extern 0 (is_true ((svd_u _)^*t \is unitarymx)) => apply: svd_u_adj_unitarymx : core.
#[global] Hint Extern 0 (is_true ((svd_v _)^*t \is unitarymx)) => apply: svd_v_adj_unitarymx : core.
#[global] Hint Extern 0 (is_true (svd_d _ \is svd_diag)) => apply: svd_d_svd_diag : core.
#[global] Hint Extern 0 (is_true (svds_d _ \is svd_diag)) => apply: svds_d_svd_diag : core.
#[global] Hint Extern 0 (is_true (0 <= fun_of_matrix (svd_d _) _ _)) => apply: svd_d_ge0 : core.
#[global] Hint Extern 0 (is_true (0 <= fun_of_matrix (svds_d _) _ _)) => apply: svds_d_ge0 : core.
#[global] Hint Extern 0 (is_true (fun_of_matrix (svd_d _) _ _ \is Num.nneg)) => apply: svd_d_nneg : core.
#[global] Hint Extern 0 (is_true (fun_of_matrix (svds_d _) _ _ \is Num.nneg)) => apply: svds_d_nneg : core.

Lemma rank_leq_min (C : fieldType) m n (A : 'M[C]_(m,n)) : (\rank A <= minn m n)%N.
Proof. by rewrite /minn; case: ltnP=> _; [apply/rank_leq_row|apply/rank_leq_col]. Qed.

(* the dim depending on rank suffers type cast problem *)
(* we thus provide any r = rank A and gives matrices with dim of r instead of rank *)
HB.lock
Definition csvdr_d (C : numClosedFieldType) m n (A : 'M[C]_(m,n)) r (eqr : \rank A = r) := 
    castmx (erefl, eqr) (lsubmx (castmx (erefl, esym (subnKC (rank_leq_min A))) (svd_d A))).
Arguments csvdr_d [C m n] A [r] eqr.
Notation csvd_d A := (csvdr_d A erefl).

HB.lock
Definition csvdr_u (C : numClosedFieldType) m n (A : 'M[C]_(m,n)) r (eqr : \rank A = r) := 
  castmx (erefl, eqr) (lsubmx (castmx (erefl, esym (subnKC (rank_leq_row A))) (svd_u A))).
Arguments csvdr_u [C m n] A [r] eqr.
Notation csvd_u A := (csvdr_u A erefl).

HB.lock
Definition csvdr_v (C : numClosedFieldType) m n (A : 'M[C]_(m,n)) r (eqr : \rank A = r) := 
  castmx (erefl, eqr) (lsubmx (castmx (erefl, esym (subnKC (rank_leq_col A))) (svd_v A))).
Arguments csvdr_v [C m n] A [r] eqr.
Notation csvd_v A := (csvdr_v A erefl).

Section compact_svd.
Variable (C : numClosedFieldType).
Implicit Type (r : nat).

Lemma usubmx_unitary m n r (U : 'M[C]_(m+n,r)) :
  U \is unitarymx -> usubmx U \is unitarymx.
Proof.
move=>/row_unitarymxP P; apply/row_unitarymxP=>i j.
by rewrite !row_usubmx P eq_lshift.
Qed.

Lemma dsubmx_unitary m n r (U : 'M[C]_(m+n,r)) :
  U \is unitarymx -> dsubmx U \is unitarymx.
Proof.
move=>/row_unitarymxP P; apply/row_unitarymxP=>i j.
by rewrite !row_dsubmx P eq_rshift.
Qed.

Lemma csvd_u_unitarymx m n (A : 'M[C]_(m,n)) r (eqr : \rank A = r) :
  (csvdr_u A eqr)^*t \is unitarymx.
Proof.
case: r / eqr; rewrite adjmxE conjmx_unitary// csvdr_u.unlock trmx_lsub.
by apply/usubmx_unitary; rewrite !castmx_funE/= trmx_unitary.
Qed.

Lemma csvd_v_unitarymx m n (A : 'M[C]_(m,n)) r (eqr : \rank A = r) :
  (csvdr_v A eqr)^*t \is unitarymx.
Proof.
case: r / eqr; rewrite adjmxE conjmx_unitary// csvdr_v.unlock trmx_lsub.
by apply/usubmx_unitary; rewrite !castmx_funE/= trmx_unitary.
Qed.

Lemma svd_d_sum m n (A : 'M[C]_(m,n)) :
  A = \sum_i svd_d A 0 i *: 
    col (cast_ord (min_idl m n) (lshift (m - n) i)) (svd_u A) *m 
      row (cast_ord (min_idr m n) (lshift (n - m) i)) (svd_v A)^*t.
Proof.
rewrite {1}(svdE A) /cdiag_mx -{1}[svd_u A](castmxK erefl (esym (min_idl m n))).
rewrite esymK castmx_mul -{1}[svd_v A](castmxK erefl (esym (min_idr m n))) esymK.
rewrite castmx_funE/= castmx_mul castmx_funE/= castmx_id.
rewrite -[castmx _ (svd_v A)^*t]vsubmxK -[castmx _ (svd_u A)]hsubmxK.
rewrite mul_row_block !mulmx0 !addr0 mul_row_col mul0mx addr0.
rewrite mulmx_colrow; apply eq_bigr=>i _.
rewrite col_diag_mul col_lsubmx row_usubmx; do ! f_equal.
by apply/matrixP=>j k; rewrite !ord1 !mxE castmxE/= cast_ord_id esymK.
by apply/matrixP=>j k; rewrite !ord1 !mxE castmxE/= cast_ord_id esymK !mxE.
Qed.

Lemma svd_diag_rank_eq0 m (v : 'rV[C]_m) (i : 'I_m) :
  v \is svd_diag -> (\rank (diag_mx v) <= i)%N -> v 0 i = 0.
Proof.
move=>Pv Pi; apply/eqP/contraT=> Pvi.
move: Pi; rewrite rank_diagmx.
suff : (i < \sum_i0 (v 0 i0 != 0)%R)%N by rewrite ltnNge=>/negP.
have Pi: (i.+1 + rev_ord i)%N = m by rewrite subnKC.
rewrite (big_split_ord_cast Pi)/=; apply/(leq_trans (n := \sum_(i0 < i.+1) 1%N)).
  by rewrite sum1_card card_ord.
apply/(leq_trans _ (leq_addr _ _))/leq_sum=>j _.
by rewrite (svd_diag_neq0 (i := i))//= -ltnS.
Qed.

Lemma svd_diag_rank_neq0 m (v : 'rV[C]_m) (i : 'I_m) :
  v \is svd_diag -> (i < \rank (diag_mx v))%N -> 0 < v 0 i.
Proof.
move=>Pv Pi; rewrite lt_def ?svd_diag_ge0// andbT; apply/eqP=>Pvi.
move: Pi; rewrite rank_diagmx.
suff : (\sum_i0 (v 0 i0 != 0)%R <= i)%N by rewrite ltnNge=>->.
have Pi: (i + (m-i))%N = m by rewrite subnKC// ltnW.
rewrite (big_split_ord_cast Pi)/=; apply/(leq_trans (n := \sum_(i0 < i) 1%N)).
  rewrite [X in (_ + X)%N]big1 ?addn0 ?leq_sum// =>j _; last by case: eqP.
    by rewrite (svd_diag_eq0 (i := i))//= ?eqxx// leq_addr.
by rewrite sum1_card card_ord.
Qed.

Lemma csvd_d_ge0 m n (A : 'M[C]_(m,n)) r (eqr : \rank A = r) i j : 
  0 <= csvdr_d A eqr i j.
Proof. by case: r / eqr j => j; rewrite csvdr_d.unlock mxE castmxE. Qed.
Lemma csvd_d_nneg m n (A : 'M[C]_(m,n)) r (eqr : \rank A = r) i j : 
  csvdr_d A eqr i j \is Num.nneg.
Proof. apply/csvd_d_ge0. Qed.

Lemma csvd_d_svd_diag m n (A : 'M[C]_(m,n)) r (eqr : \rank A = r) :
  csvdr_d A eqr \is svd_diag.
Proof.
case: r / eqr; apply/svd_diagP=>i; split=>[//|j]; first by apply/csvd_d_ge0.
case: ltnP=>// Pij /=; rewrite csvdr_d.unlock !mxE !castmxE/= ord1 esymK=> _.
by move: (svd_d_svd_diag A)=>/svd_diag_nonincreasing/rv_nonincreasingP; apply=>/=.
Qed.

Lemma rank_svd_d m n (A : 'M[C]_(m,n)) :
  \rank (diag_mx (svd_d A)) = \rank A.
Proof.
rewrite {2}(svdE A) mxrank_mulmxUC ?mxrank_mulUmx ?svd_pE//.
by rewrite /cdiag_mx castmx_funE rank_diag_block_mx mxrank0 addn0.
Qed.

Lemma csvd_d_gt0 m n (A : 'M[C]_(m,n)) r (eqr : \rank A = r) i j : 
  0 < csvdr_d A eqr i j.
Proof.
by case: r / eqr j => j; rewrite csvdr_d.unlock mxE 
  castmxE ord1/= esymK svd_diag_rank_neq0// rank_svd_d/=.
Qed.
Lemma csvd_d_pos m n (A : 'M[C]_(m,n)) r (eqr : \rank A = r) i j : 
  csvdr_d A eqr i j \is Num.pos.
Proof. apply/csvd_d_gt0. Qed.
Lemma csvd_d_posmx m n (A : 'M[C]_(m,n)) r (eqr : \rank A = r) : 
  csvdr_d A eqr \is a posmx.
Proof. by case: r / eqr; apply/posmxP=>i j; rewrite posrE csvd_d_gt0. Qed.

Lemma csvdrE m n (A : 'M[C]_(m,n)) r (eqr : \rank A = r) :
  A = csvdr_u A eqr *m diag_mx (csvdr_d A eqr) *m (csvdr_v A eqr)^*t.
Proof.
case: r / eqr; rewrite [LHS]svd_d_sum csvdr_d.unlock csvdr_u.unlock csvdr_v.unlock.
rewrite (big_split_ord_cast (subnKC (rank_leq_min A)))/= [X in _ + X]big1 ?addr0=>[i _|].
  by rewrite svd_diag_rank_eq0 ?scale0r ?mul0mx// ?svd_pE//= rank_svd_d leq_addr.
rewrite mul_mx_diag; apply/matrixP=>i j.
rewrite mxE summxE; apply eq_bigr=>r _.
rewrite !mxE big_ord1 !mxE -mulrA mulrCA mulrA !castmxE/= ?esymK ?cast_ord_id; 
by do ! f_equal; apply/val_inj=>/=.
Qed.
Arguments csvdrE [m n] A [r] eqr.

Lemma csvd_d2_svds_d m n A (U : 'M_(m,\rank A)) (v : 'rV[C]_(\rank A)) (V : 'M_(n,\rank A)) :
  U^*t \is unitarymx -> V^*t \is unitarymx -> 
    v \is svd_diag -> A = U *m diag_mx v *m V ^*t -> 
    castmx (erefl, subnKC (rank_leq_row A)) (row_mx (v .* v^*m) 0) = svds_d (A *m A^*t).
Proof.
move=>PU PV Pv PA.
move: (unitary_ext PU) (unitary_ext PV) => PU1 PV1.
apply/(svds_d_unique (U := castmx (erefl, subnKC (rank_leq_row A)) (schmidt (col_mx U^*t 0))^*t)
      (V := (castmx (subnKC (rank_leq_row A), erefl) (schmidt (col_mx U^*t 0)))^*t)).
- by rewrite -trmxC_unitary adjmx_castV/= -adjmxE adjmxK 
    castmx_funE schmidt_unitarymx// subnKC// rank_leq_row.
- by rewrite trmxC_unitary castmx_funE schmidt_unitarymx// subnKC// rank_leq_row.
- rewrite castmx_funE svd_diag_exd//; apply/svd_diagP=>i; split=>[|j Pij].
    by rewrite !mxE -normCK exprn_ge0.
  move: {+}Pv=>/svd_diag_nonincreasing/rv_nonincreasingP/(_ i j Pij) Pvij.
  by rewrite !mxE -!normCK ler_pXn2r// !ger0_norm//; apply/nnegmxP/svd_diag_nneg.
- rewrite adjmxK diagmx_cast !castmx_mul castmx_id.
  rewrite -[(schmidt _)^*t]hsubmxK -[X in (_ *m _) *m X]vsubmxK diag_mx_row.
  rewrite mul_row_col linear0 row_mx0 mulmx0 addr0.
  rewrite mul_mx_row mulmx0 mul_row_col mul0mx addr0.
  rewrite -map_lsubmx -trmx_usub -adjmxE -PU1 adjmxK [in LHS]PA.
  by rewrite  !adjmxM !mulmxA mulmxtVK// diag_mx_adj mulmxACA diag_mx_dmul.
Qed.

Lemma csvd_d_unique m n A r (eqr : \rank A = r) 
  (U : 'M_(m,r)) (v : 'rV[C]_r) (V : 'M_(n,r)) :
  U^*t \is unitarymx -> V^*t \is unitarymx -> v \is svd_diag -> 
    A = U *m diag_mx v *m V ^*t -> v = csvdr_d A eqr.
Proof.
case: r / eqr U v V => U v V PU PV Pv PA.
move: (csvd_d2_svds_d (csvd_u_unitarymx erefl) (csvd_v_unitarymx erefl) 
  (csvd_d_svd_diag erefl) (csvdrE A erefl)).
move: (csvd_d2_svds_d PU PV Pv PA)=><-/esym.
move=>/castmx_inj/eq_row_mx[]/matrixP P _.
apply/matrixP=>i j; rewrite ord1 -[LHS]ger0_norm -1?[RHS]ger0_norm ?csvd_d_ge0//.
  by apply/nnegmxP/svd_diag_nneg.
move: (P 0 j); rewrite !mxE -!normCK=>/pexpIrn; apply=>//; apply/normr_nneg.
Qed.

Lemma csvd_d_uniqueP m n r A (U : 'M_(m,r)) (v : 'rV[C]_r) (V : 'M_(n,r)) :
  U^*t \is unitarymx -> V^*t \is unitarymx -> 
    v \is svd_diag -> v \is a posmx ->
    A = U *m diag_mx v *m V ^*t -> 
    match \rank A =P r with
                   | ReflectT E => v = csvdr_d A E
                   | _ => False
    end.
Proof.
move=>PU PV Pv1 Pv2 PA.
move: {+}PA=>/(f_equal mxrank); rewrite mxrank_mulmxU// -[U]adjmxK mxrank_mulUCmx// rank_diagmx.
have Pvi i : v 0 i != 0 by rewrite gt_eqF//; apply/posmxP.
under eq_bigr do rewrite Pvi/=.
rewrite sum1_card card_ord => Pr.
case: r / Pr U v V PU PV Pv1 Pv2 PA Pvi=>U v V PU PV Pv1 Pv2 PA Pvi.
case: eqP=>// P; apply/(csvd_d_unique P PU PV Pv1 PA).
Qed.

Lemma castmx_symV T m1 n1 m2 n2 (eq_m : m1 = m2) (eq_n : n1 = n2) (A1 : 'M[T]_(m1, n1)) A2 :
  A1 = castmx (esym eq_m, esym eq_n) A2 -> A2 = castmx (eq_m, eq_n) A1.
Proof. by move=>/castmx_sym; rewrite !esymK. Qed.  

Lemma svd_d_csvdrE m n (A : 'M[C]_(m,n)) r (eqr : \rank A = r) :
  svd_d A = castmx (erefl, subnKC (rank_leq_min A)) 
    (row_mx (castmx (erefl, esym eqr) (csvdr_d A eqr)) 0).
Proof.
case: r / eqr; rewrite csvdr_d.unlock; apply/castmx_symV/matrixP=>i j.
case: (split_ordP j)=>k ->; rewrite ord1.
  by rewrite castmxE ord1/= row_mxEl mxE castmxE ord1.
rewrite castmxE/= row_mxEr ord1 esymK mxE.
symmetry; apply/svd_diag_rank_eq0; first by apply svd_d_svd_diag.
by rewrite rank_svd_d/= leq_addr.
Qed.

Lemma csvd_d_trmx m n (A : 'M[C]_(m,n)) r (eqr : _ = r) :
  csvdr_d A^T eqr = csvdr_d A (etrans (esym (mxrank_tr A)) eqr).
Proof.
rewrite csvdr_d.unlock svd_d_trmx.
case: r / eqr; rewrite castmx_id castmx_comp/=.
set P1 := etrans _ _; set P2 := esym _.
case: _ / P2 P1=>P1; rewrite castmx_id.
by move: (minnC m n)=>P2; case: _ / P2 P1=>P1; rewrite (eq_irrelevance (esym _) P1).
Qed.

Lemma csvd_d_conjmx m n (A : 'M[C]_(m,n)) r (eqr : _ = r) :
  csvdr_d A^*m eqr = csvdr_d A (etrans (esym (mxrank_conj A)) eqr).
Proof.
rewrite csvdr_d.unlock svd_d_conjmx.
case: r / eqr; rewrite castmx_id /=.
set P1 := esym _; set P2 := esym _.
by case: _ / P2 P1=>P1; rewrite castmx_id (eq_irrelevance (esym _) P1).
Qed.

Lemma csvd_d_adjmx m n (A : 'M[C]_(m,n)) r (eqr : _ = r) :
  csvdr_d A^*t eqr = csvdr_d A (etrans (esym (mxrank_adj A)) eqr).
Proof.
case: r / eqr =>/=; set P := esym _; move: P.
by rewrite adjmxTC=>P; rewrite csvd_d_conjmx csvd_d_trmx (eq_irrelevance (etrans _ _) P).
Qed.

Section csvd_col_row.

Lemma csvd_d_cast_eq m n (A : 'M[C]_(m,n)) r (eqr : \rank A = r) X :
  csvdr_d A eqr = X -> csvdr_d A erefl = castmx (erefl, esym eqr) X.
Proof. by case: r / eqr X. Qed.

Lemma csvd_d_cast_eqV m n (A : 'M[C]_(m,n)) r (eqr : \rank A = r) X :
  csvdr_d A erefl = castmx (erefl, esym eqr) X -> csvdr_d A eqr = X.
Proof. by case: r / eqr X. Qed.

Lemma csvd_d_cast m n (A : 'M[C]_(m,n)) r (eqr : \rank A = r) p (eqp : r = p) :
  castmx (erefl, eqp) (csvdr_d A eqr) = csvdr_d A (etrans eqr eqp).
Proof. by case: p / eqp. Qed.

Lemma csvd_block_mx000 m n p q (A : 'M[C]_(m,n)) r (eqr : _ = r) :
  csvdr_d (block_mx A 0 0 0 : 'M_(m+p,n+q)) eqr = csvdr_d A (etrans (esym (rank_block_mx000 _ _ A)) eqr).
Proof.
case: r / eqr; symmetry; apply/csvd_d_cast_eqV.
rewrite csvd_d_cast etrans_ereflV etrans_erefl esymK.
pose U : 'M_(m+p,_) := col_mx (csvdr_u A erefl) 0.
pose V : 'M_(n+q,_) := col_mx (csvdr_v A erefl) 0.
apply/(csvd_d_unique _ (U := U) (V := V)).
- by rewrite /U adjmxE tr_col_mx map_row_mx -!adjmxE linear0 row_mx0_unitarymx// csvd_u_unitarymx.
- by rewrite /V adjmxE tr_col_mx map_row_mx -!adjmxE linear0 row_mx0_unitarymx// csvd_v_unitarymx.
- by rewrite csvd_d_svd_diag.
- by rewrite /U /V mul_col_mx mul0mx mul_col_mx mul0mx adjmxE tr_col_mx 
  map_row_mx -!adjmxE linear0 mul_mx_row mulmx0 -csvdrE /block_mx row_mx0.
Qed.

(* Lemma block_mx_castc0 p q r (A : 'M[C]_(p,q)) (B : 'M[C]_(r,q)) :
  (col_mx A B) = castmx (erefl, addn0 q) (block_mx A 0 B 0).
Proof. by rewrite block_mxEh col_mx0 -row_mx_cast0. Qed. *)

Lemma csvd_d_col_mx0 m n p (A : 'M[C]_(m,n)) r (eqr : _ = r) :
  csvdr_d (col_mx A (0 : 'M_(p,n))) eqr = csvdr_d A (etrans (esym (rank_col_mx0 p A)) eqr).
Proof.
case: r / eqr; symmetry; apply/csvd_d_cast_eqV.
rewrite csvd_d_cast etrans_ereflV etrans_erefl esymK.
pose U : 'M_(m+p,_) := col_mx (csvdr_u A erefl) 0.
apply/(csvd_d_unique _ (U := U) (V := csvdr_v A erefl)).
- by rewrite /U adjmxE tr_col_mx map_row_mx -!adjmxE linear0 row_mx0_unitarymx// csvd_u_unitarymx.
- by rewrite csvd_v_unitarymx.
- by rewrite csvd_d_svd_diag.
- by rewrite /U mul_col_mx mul0mx mul_col_mx mul0mx -csvdrE.
Qed.

Lemma csvd_d_col_0mx m n p (A : 'M[C]_(m,n)) r (eqr : _ = r) :
  csvdr_d (col_mx (0 : 'M_(p,n)) A) eqr = csvdr_d A (etrans (esym (rank_col_0mx p A)) eqr).
Proof.
case: r / eqr; symmetry; apply/csvd_d_cast_eqV.
rewrite csvd_d_cast etrans_ereflV etrans_erefl esymK.
pose U : 'M_(p+m,_) := col_mx 0 (csvdr_u A erefl).
apply/(csvd_d_unique _ (U := U) (V := csvdr_v A erefl)).
- by rewrite /U adjmxE tr_col_mx map_row_mx -!adjmxE linear0 row_0mx_unitarymx// csvd_u_unitarymx.
- by rewrite csvd_v_unitarymx.
- by rewrite csvd_d_svd_diag.
- by rewrite /U mul_col_mx mul0mx mul_col_mx mul0mx -csvdrE.
Qed.

Lemma csvd_d_row_mx0 m n p (A : 'M[C]_(m,n)) r (eqr : _ = r) :
  csvdr_d (row_mx A (0 : 'M_(m,p))) eqr = csvdr_d A (etrans (esym (rank_row_mx0 p A)) eqr).
Proof.
case: r / eqr; set P := etrans _ _; move: P.
rewrite -[row_mx A 0]trmxK tr_row_mx linear0=>P.
by rewrite csvd_d_trmx/= csvd_d_col_mx0 csvd_d_trmx (eq_irrelevance (etrans _ _) P).
Qed.

Lemma csvd_d_row_0mx m n p (A : 'M[C]_(m,n)) r (eqr : _ = r) :
  csvdr_d (row_mx (0 : 'M_(m,p)) A) eqr = csvdr_d A (etrans (esym (rank_row_0mx p A)) eqr).
Proof.
case: r / eqr; set P := etrans _ _; move: P.
rewrite -[row_mx 0 A]trmxK tr_row_mx linear0=>P.
by rewrite csvd_d_trmx/= csvd_d_col_0mx csvd_d_trmx (eq_irrelevance (etrans _ _) P).
Qed.

End csvd_col_row.
End compact_svd.

Arguments csvd_u_unitarymx [C m n] A [r] eqr.
Arguments csvd_v_unitarymx [C m n] A [r] eqr.
Arguments csvd_d_ge0 [C m n] A [r] eqr.
Arguments csvd_d_nneg [C m n] A [r] eqr.
Arguments csvd_d_svd_diag [C m n] A [r] eqr.
Arguments csvd_d_gt0 [C m n] A [r] eqr.
Arguments csvd_d_pos [C m n] A [r] eqr.
Arguments csvd_d_posmx [C m n] A [r] eqr.
Arguments csvdrE [C m n] A [r] eqr.
Notation csvdE A := (csvdrE A erefl).
Arguments csvd_d_unique [C m n] A [r] eqr.
Arguments svd_d_csvdrE [C m n] A [r] eqr.
Notation svd_d_csvdE A := (svd_d_csvdrE A erefl).
Arguments csvd_d_trmx [C m n] A [r] eqr.
Arguments csvd_d_conjmx [C m n] A [r] eqr.
Arguments csvd_d_adjmx [C m n] A [r] eqr.

#[global] Hint Extern 0 (is_true ((csvdr_u _ _)^*t \is unitarymx)) => apply: csvd_u_unitarymx : core.
#[global] Hint Extern 0 (is_true ((csvdr_v _ _)^*t \is unitarymx)) => apply: csvd_v_unitarymx : core.
#[global] Hint Extern 0 (is_true ((csvdr_d _ _)\is svd_diag)) => apply: csvd_d_svd_diag : core.
#[global] Hint Extern 0 (is_true ((csvdr_d _ _)\is a posmx)) => apply: csvd_d_posmx : core.
#[global] Hint Extern 0 (is_true (0 <= fun_of_matrix (csvdr_d _ _) _ _)) => apply: csvd_d_ge0 : core.
#[global] Hint Extern 0 (is_true (0 < fun_of_matrix (csvdr_d _ _) _ _)) => apply: csvd_d_gt0 : core.
#[global] Hint Extern 0 (is_true (fun_of_matrix (csvdr_d _ _) _ _ \is Num.nneg)) => apply: csvd_d_nneg : core.
#[global] Hint Extern 0 (is_true (fun_of_matrix (csvdr_d _ _) _ _ \is Num.pos)) => apply: csvd_d_pos : core.
#[global] Hint Extern 0 (is_true (fun_of_matrix (svds_d _) _ _ \is Num.nneg)) => apply: svds_d_nneg : core.

Section vonNeumann_trace.

Section shift.
Variable (R : numFieldType).

Definition telescope_fun_ord (n : nat) (f : 'I_n.+1 -> R) (i : 'I_n.+1) :=
  f i - frcons (ftail f) 0 i.

Lemma telescope_fun_ord_fcons n x f : 
  @telescope_fun_ord n.+1 (fcons x f) = fcons (x - f 0) (telescope_fun_ord f).
Proof.
rewrite /telescope_fun_ord; apply/funext=>i.
case: (unliftP ord0 i)=>/=[j ->|->].
  rewrite !fconsE fconsKV; do ! f_equal; 
  case: (unliftP ord_max j)=>/=[k ->|->].
    have -> : (nlift ord0 (nlift ord_max k)) = nlift ord_max (nlift ord0 k).
      by apply/val_inj=>/=; rewrite !bump0 bumpS.
    by rewrite !frconsE.
  have -> : nlift ord0 ord_max = ord_max :> 'I_n.+2 by apply/val_inj.
  by rewrite !frcons_max.
rewrite !fcons0.
have ->: ord0 = nlift ord_max ord0 :> 'I_n.+2 by apply/val_inj.
by rewrite frconsE fconsKV.
Qed.

Lemma telescope_fun_ord_sum (n : nat) (f : 'I_n.+1 -> R) :
  forall i : 'I_n.+1, f i = \sum_j telescope_fun_ord f j * (i <= j)%:R.
Proof.
elim: n f=>[f i|n IH f].
  rewrite big_ord1 /telescope_fun_ord !ord1 leqnn mulr1.
  have -> : 0 = ord_max :> 'I_1 by rewrite ord1.
  by rewrite frcons_max subr0.
case: (fconsP f); clear f => x f i.
case: (unliftP ord0 i)=>[/=j ->|->].
  rewrite fconsE big_ord_recl/= mulr0 add0r {1}IH; apply eq_bigr=>k _.
  by rewrite telescope_fun_ord_fcons fconsE !bump0/= ltnS.
rewrite fcons0 big_ord_recl telescope_fun_ord_fcons fcons0 leqnn mulr1.
apply/eqP; rewrite addrC -subr_eq subKr {1}IH/=.
by apply/eqP; apply eq_bigr=>j _; rewrite !mulr1 fconsE.
Qed.
End shift.

Variable (R : numClosedFieldType).

(* von Neumann trace inequality *)
Lemma vonNeumann_trace_ler m (A B : 'M[R]_m): 
  `| \tr (A *m B) | <= \sum_i (svds_d A 0 i) * (svds_d B 0 i).
Proof.
case: m A B=>[??|m A B].
  by rewrite !mx_dim0E mxtrace0 normr0 sumr_ge0// =>?; rewrite mxE mulr0.
rewrite {1}(svdsE A) {1}(svdsE B) -!mulmxA mxtrace_mulC -!mulmxA [_^*t *m _]mulmxA.
set U := _^*t *m _. set V := _ ^*t *m _.
pose P (i : 'I_m.+1) := diag_mx (\row_(j < m.+1) (j <= i)%:R) : 'M[R]_m.+1.
pose a (x : 'M[R]_m.+1) := telescope_fun_ord (svds_d x 0).
have Pa x : diag_mx (svds_d x) = \sum_i (a x i) *: (P i).
  transitivity (diag_mx (\sum_i (a x i) *: (\row_(j < m.+1) (j <= i)%:R))); last first.
    apply/matrixP=>i j; rewrite mxE !summxE.
    case: eqP=>[->|/eqP/negPf Pij]; 
      first by rewrite mulr1n; apply eq_bigr=>k _; rewrite !mxE eqxx mulr1n.
    by rewrite mulr0n big1// =>k _; rewrite !mxE Pij mulr0n mulr0.
  f_equal; apply/matrixP=>i j; rewrite ord1 summxE.
  under eq_bigr do rewrite !mxE /a. apply: telescope_fun_ord_sum.
have Pa_ge0 x i : 0 <= a x i.
  rewrite /a /telescope_fun_ord; case: (unliftP ord_max i)=>/=[j->|->].
    rewrite frconsE /ftail subr_ge0.
    move: (svds_d_svd_diag x)=>/svd_diagP/(_ (nlift ord_max j))[] _ /(_ (nlift 0 j)).
    by apply; rewrite lift_max lift0.
  by rewrite frcons_max subr0.
rewrite !Pa linear_suml/=.
under eq_bigr do rewrite linear_suml/= !linear_sumr/=.
rewrite pair_big/= linear_sum/=.
under eq_bigr do rewrite -!scalemxAl -!scalemxAr scalerA linearZ/=.
have -> : \sum_(i < m.+1) svds_d A 0 i * svds_d B 0 i = 
          \sum_i (a A i.1) * (a B i.2) * \tr(P i.1 *m P i.2).
  transitivity (\tr (diag_mx (svds_d A) *m diag_mx (svds_d B))).
    by rewrite mul_mx_diag /mxtrace; apply eq_bigr=>/= i _; rewrite !mxE eqxx mulr1n.
  rewrite !Pa pair_bigV linear_suml/= linear_sum; apply eq_bigr=>i _ /=.
  rewrite linear_sumr linear_sum; apply eq_bigr =>j _ /=.
  by rewrite -scalemxAl -scalemxAr scalerA linearZ.
apply/(le_trans (ler_norm_sum _ _ _))/ler_sum=>[[i j]] _ /=.
rewrite normrM ger0_norm ?ler_wpM2l ?mulr_ge0//.
have: U \is unitarymx by rewrite unitarymx_mulmx_closed.
have: V \is unitarymx by rewrite unitarymx_mulmx_closed.
wlog : i j U V / (i <= j)%N => [IH PV PU|Pij PV PU].
  case: (leqP i j)=>[/IH/(_ PV)/(_ PU)//|/ltnW/IH/(_ PU)/(_ PV)].
  by rewrite mulmxA mxtrace_mulC [X in _ <= X -> _]mxtrace_mulC mulmxA.
rewrite [P i *m (_ *m _)]mulmx_colrow linear_sum/= diag_mx_dmul mxtrace_diag.
apply/(le_trans (ler_norm_sum  _ _ _))/ler_sum=>k _.
rewrite !mxE mxtrace_mulC; apply/(le_trans (l2normC_cauchy _ _)).
rewrite mulmxA row_mul l2normCUr ?PV// row_mul.
have P1 : l2normC (row k U *m P j) <= 1.
  apply/(le_trans (y := l2normC (row k U))); last first.
    by rewrite l2normC_unitary ?sqrtC1// row_unitarymx.
  rewrite !l2normC_dot ler_sqrtC ?nnegrE.
    1,2: by rewrite dot_l2normC exprn_ge0 ?normv_ge0.
  rewrite adjmxM mulmxA mulmxACA diag_mx_adj diag_mx_dmul mul_mx_diag !trace_mx11 !mxE.
  apply ler_sum=>b _; rewrite !mxE mulrAC ler_piMr// -?normCK// ?exprn_ge0//.
  by case: leqP; rewrite ?normr1 ?expr1n// normr0 expr0n.
have -> : l2normC (col k (P i)) = (k <= i)%:R.
  rewrite l2normC_dot mxtrace_mulC trace_mx11 mxE/= (bigD1 k)//= big1.
  by move=>l /negPf Pl; rewrite !mxE Pl mulr0n mulr0.
  by rewrite !mxE eqxx mulr1n addr0 -normCKC sqrCK// ger0_norm.
apply/(le_trans (ler_wpM2r _ P1))=>//.
by rewrite mul1r; case: leqP=>[Pk|]; rewrite ?mul0r// (leq_trans Pk Pij) mulr1.
Qed.

End vonNeumann_trace.

(* to avoid messy type cast of singular values *)
HB.lock Definition svd_f (C : numClosedFieldType) m n (A : 'M[C]_(m,n)) (i : nat) :=
  match (i < minn m n)%N =P true with
  | ReflectT E => svd_d A 0 (Ordinal E) | _ => 0 
  end.

Section svd_f.
Variable (C : numClosedFieldType).

Lemma svd_dE m n (A : 'M[C]_(m,n)) i j : svd_d A i j = svd_f A j.
Proof.
by rewrite svd_f.unlock ord1; case: j=>j Pj; 
  case: eqP=>//= P; rewrite (eq_irrelevance P Pj).
Qed.

Lemma svd_dEV m n (A : 'M[C]_(m,n)) (j : 'I_(minn m n)) : svd_f A j = svd_d A 0 j.
Proof. by rewrite svd_dE. Qed.

Lemma svds_dE m (A : 'M[C]_m) i j : svds_d A i j = svd_f A j.
Proof. by rewrite ord1 /svds_d castmxE/= svd_dE. Qed.

Lemma svds_dEV m (A : 'M[C]_m) (j : 'I_m) : svd_f A j = svds_d A 0 j.
Proof. by rewrite svds_dE. Qed.

Lemma csvdr_dE m n (A : 'M[C]_(m,n)) r (eqr : \rank A = r) i j : 
  csvdr_d A eqr i j = svd_f A j.
Proof. by rewrite csvdr_d.unlock castmxE mxE castmxE svd_dE. Qed.

Lemma csvdr_dEV m n (A : 'M[C]_(m,n)) r (eqr : \rank A = r) i (j : 'I_r) : 
  svd_f A j = csvdr_d A eqr i j.
Proof. by rewrite csvdr_dE. Qed.

Lemma svd_f_nincr m n (A : 'M[C]_(m,n)) i j :
  (i <= j)%N -> svd_f A j <= svd_f A i.
Proof.
move=>Pij; rewrite svd_f.unlock; case: eqP=>Pj; case: eqP=>Pi//.
by apply/rv_nonincreasingP=>//; apply/svd_diag_nonincreasing.
by move: (leq_ltn_trans Pij Pj).
Qed.

Lemma svd_f_ge0 m n (A : 'M[C]_(m,n)) i : 0 <= svd_f A i.
Proof. by rewrite svd_f.unlock; case: eqP. Qed.

Lemma svd_f_nneg m n (A : 'M[C]_(m,n)) i : svd_f A i \is Num.nneg.
Proof. by rewrite nnegrE svd_f_ge0. Qed.

Lemma svd_f_gt0 m n (A : 'M[C]_(m,n)) i : (i < \rank A)%N -> 0 < svd_f A i.
Proof. by move=>P; move: (csvd_d_gt0 A erefl 0 (Ordinal P)); rewrite csvdr_dE. Qed.

Lemma svd_f_eq0 m n (A : 'M[C]_(m,n)) i : (\rank A <= i)%N -> svd_f A i = 0.
Proof.
move=>Pi; rewrite svd_f.unlock; case: eqP=>// P.
apply/svd_diag_rank_eq0; first by apply/svd_d_svd_diag.
by rewrite rank_svd_d.
Qed.

Lemma svd_f_pos m n (A : 'M[C]_(m,n)) i : (i < \rank A)%N -> svd_f A i \is Num.pos.
Proof. rewrite posrE; exact: svd_f_gt0. Qed.

Lemma svd_d_exdrE m n (A : 'M[C]_(m,n)) i j : 
  svd_d_exdr (svd_d A) i j = svd_f A j.
Proof.
rewrite castmxE/= ord1 mxE; case: split_ordP.
by move=>k /(f_equal val); rewrite svd_dE/==>->.
move=>k /(f_equal val)/= ->; rewrite mxE svd_f_eq0//.
apply/(leq_trans (rank_leq_min _))/leq_addr.
Qed.

Lemma svd_d_exdlE m n (A : 'M[C]_(m,n)) i j : 
  svd_d_exdl (svd_d A) i j = svd_f A j.
Proof.
rewrite castmxE/= ord1 mxE; case: split_ordP.
by move=>k /(f_equal val); rewrite svd_dE/==>->.
move=>k /(f_equal val)/= ->; rewrite mxE svd_f_eq0//.
apply/(leq_trans (rank_leq_min _))/leq_addr.
Qed.

Lemma svd_f_eq m n (A B : 'M[C]_(m,n)) :
  svd_d A = svd_d B -> svd_f A = svd_f B.
Proof. by move=>/matrixP P; rewrite svd_f.unlock; apply/funext=>i; case: eqP. Qed.

Lemma csvd_f_eq m n (A : 'M[C]_(m,n)) m' n' (B : 'M[C]_(m',n')) (r : nat)
  (eqr1 : \rank A = r) (eqr2 : \rank B = r) :
  csvdr_d A eqr1 = csvdr_d B eqr2 -> svd_f A = svd_f B.
Proof.
move=>/matrixP P; apply/funext=>i .
have [] := ltnP i r.
  by move=>Pi; move: (P 0 (Ordinal Pi)); rewrite !csvdr_dE.
by move=>Pr; rewrite !svd_f_eq0// ?eqr1 ?eqr2.
Qed.

Lemma svd_f_trmx m n (A : 'M[C]_(m,n)) : svd_f A^T = svd_f A.
Proof. move: (csvd_d_trmx A erefl); apply csvd_f_eq. Qed.

Lemma svd_f_conjmx m n (A : 'M[C]_(m,n)) : svd_f A^*m = svd_f A.
Proof. apply/svd_f_eq/svd_d_conjmx. Qed.

Lemma svd_f_adjmx m n (A : 'M[C]_(m,n)) : svd_f A^*t = svd_f A.
Proof. by rewrite adjmxTC svd_f_conjmx svd_f_trmx. Qed.

Lemma svd_f_Ul m n (U : 'M_m) (A : 'M[C]_(m,n)) : 
  U \is unitarymx -> svd_f (U *m A) = svd_f A.
Proof. by move=>UU; apply/svd_f_eq/svd_d_Ul. Qed.

Lemma svd_f_Ur m n (U : 'M_n) (A : 'M[C]_(m,n)) : 
  U \is unitarymx -> svd_f (A *m U) = svd_f A.
Proof. by move=>UU; apply/svd_f_eq/svd_d_Ur. Qed.

Lemma svd_f_Ul_cond r m n (U : 'M_(r,m)) (A : 'M[C]_(m,n)) : 
  U \is unitarymx -> r = m -> svd_f (U *m A) = svd_f A.
Proof. by move=>UU Pm; case: m / Pm U A UU; exact: svd_f_Ul. Qed.

Lemma svd_f_Ur_cond r m n (U : 'M_(n,r)) (A : 'M[C]_(m,n)) : 
  U \is unitarymx -> n = r -> svd_f (A *m U) = svd_f A.
Proof. by move=>UU Pr; case: r / Pr U UU=>U; apply: svd_f_Ur. Qed.

Lemma svd_f_block_mx000 m n p q (A : 'M[C]_(m,n)) :
  svd_f (block_mx A 0 0 0 : 'M_(m+p,n+q)) = svd_f A.
Proof. by move: (@csvd_block_mx000 C m n p q A _ erefl); apply/csvd_f_eq. Qed.

Lemma svd_f_col_mx0 m n p (A : 'M[C]_(m,n)) :
  svd_f (col_mx A (0 : 'M_(p,n))) = svd_f A.
Proof. by move: (@csvd_d_col_mx0 C m n p A _ erefl); apply/csvd_f_eq. Qed.

Lemma svd_f_col_0mx m n p (A : 'M[C]_(m,n)) :
  svd_f (col_mx (0 : 'M_(p,n)) A) = svd_f A.
Proof. by move: (@csvd_d_col_0mx C m n p A _ erefl); apply/csvd_f_eq. Qed.

Lemma svd_f_row_mx0 m n p (A : 'M[C]_(m,n)) :
  svd_f (row_mx A (0 : 'M_(m,p))) = svd_f A.
Proof. by move: (@csvd_d_row_mx0 C m n p A _ erefl); apply/csvd_f_eq. Qed.

Lemma svd_f_row_0mx m n p (A : 'M[C]_(m,n)) :
  svd_f (row_mx (0 : 'M_(m,p)) A) = svd_f A.
Proof. by move: (@csvd_d_row_0mx C m n p A _ erefl); apply/csvd_f_eq. Qed.

Lemma svd_f0 m n : svd_f (0 : 'M[C]_(m,n)) = fun=>0.
Proof.
rewrite svd_f.unlock; apply/funext=>i; case: eqP=>// P.
by rewrite svd_d0 mxE.
Qed.

End svd_f.

#[global] Hint Extern 0 (is_true (0 <= svd_f _ _)) => apply: svd_f_ge0 : core.
#[global] Hint Extern 0 (is_true (svd_f _ _ \is Num.nneg)) => apply: svd_f_nneg : core.

(* Courant-Fischer theorem for svd decomposition *)
Section Courant_Fischer.
Variable (C : numClosedFieldType).
Import VectorInternalTheory.

Theorem svd_minmax_ub m n (A : 'M[C]_(m,n)) (k : nat) (P : 'M_(k,n)) :
  exists x : 'cV_n, (P *m x = 0) /\ 
   svd_f A k <= l2normC (A *m x) / l2normC x.
Proof.
have [Pk|] := boolP (k < minn m n)%N; last first.
  rewrite -leqNgt=>Pk; exists 0; rewrite !mulmx0 normv0 mul0r svd_f_eq0//.
  by apply/(leq_trans _ Pk)/rank_leq_min.
have P1 : (\rank P <= k)%N by apply rank_leq_row.
pose Q := (ortho (@conjCfun C) 1%:M P).
have Q1 : ((n - k) <= \rank Q)%N by rewrite rank_ortho leq_sub2l.
have c1 : (k.+1 <= n)%N by apply/(leq_trans Pk)/geq_minr.  
pose Vk := \matrix_(i < k.+1, j < n) (svd_v A)^*t (widen_ord c1 i) j.
have Vk_row i : row i Vk = row (widen_ord c1 i) (svd_v A)^*t.
  by apply/matrixP=>a b; rewrite !mxE.
move: (svd_v_unitarymx A); rewrite -adjmx_unitary=>/row_unitarymxP Q2.
have Vk_u : Vk \is unitarymx.
  by apply/row_unitarymxP=>i j; rewrite !Vk_row Q2 -(inj_eq val_inj)/=.
have Vk_rank : \rank Vk = k.+1 by rewrite mxrank_unitary.
have P2 : (\rank (Q + Vk)%MS < \rank Q + \rank Vk)%N.
  apply/(leq_ltn_trans (n := n)); first by apply/rank_leq_col.
  by rewrite Vk_rank addnS ltnS addnC -leq_subLR.
move: (mxrank_adds_leqif Q Vk)=>/ltn_leqif; rewrite P2 submx0=>/esym/negP/negP P3.
move: {+}P3=>/rowV0Pn[v Pv1 Pv2].
exists v^*t; do ! split.
  move: Pv1; rewrite sub_capmx=>/andP[]+ _.
  by rewrite orthomx1E -adjmxE=>/eqP P4; rewrite -[LHS]adjmxK adjmxM adjmxK P4 linear0.
move: Pv1; rewrite sub_capmx=>/andP[] _ /submxP [d] Pd.
rewrite ler_pdivlMr ?l2normC_adjmx ?normv_gt0// {2}(svdE A) -!mulmxA 
  l2normCUl// -adjmxM -[in leLHS](l2normCUr (U := svd_v A))//.
set w := _ *m _.
rewrite -(ler_pXn2r (n := 2))// ?nnegrE// ?mulr_ge0// exprMn -l2normC_adjmx.
rewrite -!dot_l2normC adjmxM !mulmxA [in leRHS]mxtrace_mulC !mulmxA cdiag_mx_mulr adjmxK.
rewrite -mulmxA mul_diag_mx /mxtrace mulr_sumr/= ler_sum// => i _.
rewrite mxE svd_d_exdr_conj 2 ![in leRHS]mxE svd_d_exdrE -normCKC.
rewrite mulmx_rowcol mxE/= big_ord1 mxE mxE mxE [col _ _ _ _]mxE -normCKC.
have [Pi |] := boolP (i < k.+1)%N.
  by apply/ler_pM=>//; rewrite ?exprn_ge0// ler_pXn2r// ?nnegrE// ger0_norm// svd_f_nincr.
rewrite -leqNgt=>Pi.
rewrite /w Pd -mulmxA mxE big1 ?normr0 ?expr0n/= ?mulr0// =>j _.
rewrite -[svd_v A]adjmxK dot_dotmxE Vk_row Q2; move: Pi.
case: eqP=>[ <- /=|]; last by rewrite mulr0.
by rewrite ltnNge -ltnS ltn_ord.
Qed.

Theorem svd_minmax_lb m n (A : 'M[C]_(m,n)) (k : nat) :
  exists (P : 'M_(k,n)), forall x : 'cV_n, 
    (P *m x = 0) -> l2normC (A *m x) <= svd_f A k * l2normC x .
Proof.
have [c1|] := boolP (k <= n)%N; last first.
  rewrite -ltnNge=>/ltnW/subnKC<-.
  exists (col_mx 1%:M 0)=> x /eqP; rewrite mul_col_mx mul1mx col_mx_eq0;
  by move=>/andP[]/eqP-> _; rewrite mulmx0 !normv0 mulr0.
pose P := \matrix_(i < k, j < n) (svd_v A)^*t (widen_ord c1 i) j.
have P_row i : row i P = row (widen_ord c1 i) (svd_v A)^*t.
  by apply/matrixP=>a b; rewrite !mxE.
exists P=>x.
have [/eqP -> | Px0 Px ] := boolP (x == 0).
  by rewrite !mulmx0 !normv0 mulr0.
rewrite -(ler_pXn2r (n := 2))// ?nnegrE// ?mulr_ge0//.
rewrite exprMn {1}(svdE A) -!mulmxA l2normCUl// -[in leRHS](l2normCUl (U := (svd_v A)^*t))//.
rewrite -!dot_l2normC adjmxM !mulmxA mxtrace_mulC !mulmxA cdiag_mx_mulr mulmxACA.
set y := (svd_v A)^*t *m x.
rewrite -mulmxA mul_diag_mx /mxtrace mulr_sumr ler_sum//==>i _.
rewrite mxE mxE svd_d_exdr_conj mxE svd_d_exdrE -normCKC ger0_norm//.
have [Pi |] := boolP (k <= i)%N.
  apply/ler_pM=>//; rewrite ?exprn_ge0// ?ler_pXn2r// ?nnegrE// ?svd_f_nincr//.
  by rewrite mxE big_ord1 2![in X in _ * X]mxE -normCK exprn_ge0.
rewrite -ltnNge=>Pi. rewrite mxE big1 ?mulr0//==>j _.
rewrite 2![in X in _ * X]mxE -normCK ord1 /y mulmx_rowcol.
move: Px=>/matrixP/(_ (Ordinal Pi) 0); rewrite [(P *m x) _ _]mulmx_rowcol P_row.
have ->: (widen_ord c1 (Ordinal Pi)) = i by apply/val_inj.
by move=>->; rewrite mxE normr0 expr0n.
Qed.

Theorem svd_maxmin_lb m n (A : 'M[C]_(m,n)) (k : 'I_n) (P : 'M_(rev_ord k,n)) :
  (0 < n)%N -> exists x : 'cV_n, (P *m x = 0) /\ l2normC x != 0 /\
   l2normC (A *m x) / l2normC x <= svd_f A k.
Proof.
case: n A k P=>// n A k P _.
have c1 : (k + (rev_ord k).+1 = n.+1)%N by rewrite addnS -addSn addnC/= subnK.
have P1 : (\rank P <= rev_ord k)%N by apply rank_leq_row.
pose Q := (ortho (@conjCfun C) 1%:M P).
have Q1 : (k.+1 <= \rank Q)%N.
  by rewrite rank_ortho ltn_subRL -{5}c1 addnC ltn_add2l ltnS.
pose Vk := dsubmx (castmx (esym c1, erefl) ((svd_v A)^*t)).
have Vk_u : Vk \is unitarymx by apply/dsubmx_unitary; rewrite castmx_funE.
have Vk_rank : \rank Vk = (rev_ord k).+1 by rewrite mxrank_unitary.
have P2 : (\rank (Q + Vk)%MS < \rank Q + \rank Vk)%N.
  apply/(leq_ltn_trans (n := n.+1)); first by apply/rank_leq_col.
  by rewrite Vk_rank -{1}c1 ltn_add2r.
move: (mxrank_adds_leqif Q Vk)=>/ltn_leqif; rewrite P2 submx0=>/esym/negP/negP P3.
move: {+}P3=>/rowV0Pn[v Pv1 Pv2].
exists v^*t; do ! split.
  move: Pv1; rewrite sub_capmx=>/andP[]+ _.
  by rewrite orthomx1E -adjmxE=>/eqP P4; rewrite -[LHS]adjmxK adjmxM adjmxK P4 linear0.
  by rewrite l2normC_adjmx normv_eq0.
move: Pv1; rewrite sub_capmx=>/andP[] _ /submxP [d] Pd.
rewrite ler_pdivrMr ?l2normC_adjmx ?normv_gt0// {1}(svdE A) -!mulmxA
  l2normCUl// -adjmxM -[in leRHS](l2normCUr (U := svd_v A))//.
set w := v *m _.
rewrite -(ler_pXn2r (n := 2))// ?nnegrE// ?mulr_ge0// exprMn -[in leRHS]l2normC_adjmx.
rewrite -!dot_l2normC adjmxM !mulmxA [in leLHS]mxtrace_mulC !mulmxA cdiag_mx_mulr adjmxK.
rewrite -mulmxA mul_diag_mx /mxtrace mulr_sumr/= ler_sum// => i _.
rewrite mxE svd_d_exdr_conj 2 ![in leLHS]mxE svd_d_exdrE -normCKC.
rewrite mulmx_rowcol mxE/= big_ord1 mxE mxE mxE [col _ _ _ _]mxE -normCKC.
have [Pi |Pi] := leqP k i.
  by apply/ler_pM=>//; rewrite ?exprn_ge0// ler_pXn2r// ?nnegrE// ger0_norm// svd_f_nincr.
rewrite /w Pd -mulmxA mxE big1 ?normr0 ?expr0n/= ?mulr0// =>j _.
rewrite mul_dsub_mx castmx_mull unitarymxKV// !mxE castmxE/= cast_ord_id esymK mxE.
case: eqP=>[Pj|]; last by rewrite mulr0.
by move: Pi; rewrite -Pj/= -ltn_subRL subnn.
Qed.

Theorem svd_maxmin_ub m n (A : 'M[C]_(m,n)) (k : 'I_n) :
  exists (P : 'M_(rev_ord k,n)), forall x : 'cV_n, 
    (P *m x = 0) -> svd_f A k * l2normC x <= l2normC (A *m x).
Proof.
case: n A k => [?[]//| n A k].
have c1 : (k.+1 + rev_ord k = n.+1)%N by rewrite /= addnC subnK.
pose P := dsubmx (castmx (esym c1, erefl) ((svd_v A)^*t)).
exists P=>x.
have [/eqP -> | Px0 Px ] := boolP (x == 0).
  by rewrite !mulmx0 !normv0 mulr0.
rewrite -(ler_pXn2r (n := 2))// ?nnegrE// ?mulr_ge0//.
rewrite exprMn {2}(svdE A) -!mulmxA l2normCUl// -[in leLHS](l2normCUl (U := (svd_v A)^*t))//.
set y := (svd_v A)^*t *m x.
rewrite -!dot_l2normC adjmxM mulmxA [leRHS]mxtrace_mulC 2!mulmxA cdiag_mx_mulr.
rewrite -mulmxA mul_diag_mx /mxtrace mulr_sumr ler_sum//==>i _.
rewrite svd_d_exdr_conj 3![in leRHS]mxE svd_d_exdrE -normCKC ger0_norm//.
have [Pi | Pi ] := leqP i k.
  apply/ler_pM=>//; rewrite ?exprn_ge0// ?ler_pXn2r// ?nnegrE// ?svd_f_nincr//.
  by rewrite mxE big_ord1 2![in X in _ * X]mxE -normCK exprn_ge0.
rewrite mxE big1 ?mulr0//==>j _; 
rewrite 2![in X in _ * X]mxE -normCK ord1 /y.
have i1 : (i - k.+1 < rev_ord k)%N by rewrite /= ltn_sub2rE.
have -> : i = cast_ord c1 (rshift k.+1 (Ordinal i1)).
  by apply/val_inj=>/=; rewrite addnC subnK.
move: Px; rewrite mul_dsub_mx=>/matrixP/(_ (Ordinal i1) 0).
by rewrite mxE castmx_mull castmxE/= ord1 esymK=>->; rewrite mxE normr0 expr0n.
Qed.

Lemma l2normC_col''0 [R : numClosedFieldType] [m n] j (A : 'M[R]_(m,n.-1)) : 
  l2normC (col'' j A 0) = l2normC A.
Proof. by rewrite !l2normC_dot adjmx_col'' mulmx_colrow'' mul0mx addr0. Qed.

Lemma l2normC_row''0 [R : numClosedFieldType] [m n] j (A : 'M[R]_(m.-1,n)) : 
  l2normC (row'' j A 0) = l2normC A.
Proof. by rewrite -l2normC_trmx tr_row'' linear0 l2normC_col''0 l2normC_trmx. Qed.

Lemma svd_f_col' m n (A : 'M[C]_(m,n)) i (k : nat) :
  svd_f (col' i A) k <= svd_f A k.
Proof.
move: (svd_minmax_lb A k)=>[P Px].
move: (svd_minmax_ub (col' i A) (col' i P))=>[x [Px1]] /le_trans; apply.
pose y := row'' i x 0.
have P1 : P *m y = 0 by rewrite -[P](col''K i) /y mulmx_colrow'' mulmx0 addr0.
have -> : l2normC (col' i A *m x) = l2normC (A *m y).
  by rewrite -{2}[A](col''K i) mulmx_colrow'' mulmx0 addr0.
have [/eqP ->|Pn] := boolP (l2normC x == 0).
  by rewrite invr0 mulr0.
by rewrite ler_pdivrMr ?lt_def ?Pn//= -[_ x](l2normC_row''0 i); apply Px.
Qed.

Lemma svd_f_row' m n (A : 'M[C]_(m,n)) i (k : nat) :
  svd_f (row' i A) k <= svd_f A k.
Proof. by rewrite -svd_f_trmx tr_row' -[in leRHS]svd_f_trmx svd_f_col'. Qed.

Lemma svd_f_cast m n m' n' (A : 'M[C]_(m,n)) (eqmn : (m = m') * (n = n')) :
  svd_f (castmx eqmn A) = svd_f A.
Proof. by rewrite castmx_funE. Qed.

Lemma svd_f_row_mxl m n r (A : 'M[C]_(m,n)) (B : 'M_(m,r)) i :
  svd_f A i <= svd_f (row_mx A B) i.
Proof.
move: r B i n A; apply: row_ind.
by move=>n A i B; rewrite mx_dim0E svd_f_row_mx0.
move=>r c A IH i n B; rewrite row_mxA svd_f_cast.
apply/(le_trans _ (IH _ _ _)).
apply/(le_trans _ (svd_f_col' _ (rshift _ 0) _)).
by rewrite col'Kr svd_f_cast mx_dim0E svd_f_row_mx0.
Qed.

Lemma svd_f_row_mxr m n r (A : 'M[C]_(m,n)) (B : 'M_(m,r)) i :
  svd_f B i <= svd_f (row_mx A B) i.
Proof. by rewrite row_mx_perm svd_f_cast svd_f_Ur ?perm_mx_unitary// svd_f_row_mxl. Qed.

Lemma svd_f_col_mxl m n r (A : 'M[C]_(m,n)) (B : 'M_(r,n)) i :
  svd_f A i <= svd_f (col_mx A B) i.
Proof.
rewrite -[in leRHS]svd_f_trmx tr_col_mx.
by apply/(le_trans _ (svd_f_row_mxl _ _ _)); rewrite svd_f_trmx.
Qed.

Lemma svd_f_col_mxr m n r (A : 'M[C]_(m,n)) (B : 'M_(r,n)) i :
  svd_f B i <= svd_f (col_mx A B) i.
Proof.
rewrite -[in leRHS]svd_f_trmx tr_col_mx.
by apply/(le_trans _ (svd_f_row_mxr _ _ _)); rewrite svd_f_trmx.
Qed.

Lemma svd_f_block_mxul m n p q (A : 'M[C]_(m,n)) B D (E : 'M_(p,q)) i :
  svd_f A i <= svd_f (block_mx A B D E) i.
Proof. by apply/(le_trans _ (svd_f_col_mxl _ _ _))/svd_f_row_mxl. Qed.

Lemma svd_f_block_mxur m n p q (A : 'M[C]_(m,n)) B D (E : 'M_(p,q)) i :
  svd_f B i <= svd_f (block_mx A B D E) i.
Proof. by apply/(le_trans _ (svd_f_col_mxl _ _ _))/svd_f_row_mxr. Qed.

Lemma svd_f_block_mxdl m n p q (A : 'M[C]_(m,n)) B D (E : 'M_(p,q)) i :
  svd_f D i <= svd_f (block_mx A B D E) i.
Proof. by apply/(le_trans _ (svd_f_col_mxr _ _ _))/svd_f_row_mxl. Qed.

Lemma svd_f_block_mxdr m n p q (A : 'M[C]_(m,n)) B D (E : 'M_(p,q)) i :
  svd_f E i <= svd_f (block_mx A B D E) i.
Proof. by apply/(le_trans _ (svd_f_col_mxr _ _ _))/svd_f_row_mxr. Qed.

Lemma svd_f_usub m n p (A : 'M[C]_(m+n,p)) i :
  svd_f (usubmx A) i <= svd_f A i.
Proof. by rewrite -{2}[A]vsubmxK svd_f_col_mxl. Qed.

Lemma svd_f_dsub m n p (A : 'M[C]_(m+n,p)) i :
  svd_f (dsubmx A) i <= svd_f A i.
Proof. by rewrite -{2}[A]vsubmxK svd_f_col_mxr. Qed.

Lemma svd_f_lsub m n p (A : 'M[C]_(m,n+p)) i :
  svd_f (lsubmx A) i <= svd_f A i.
Proof. by rewrite -{2}[A]hsubmxK svd_f_row_mxl. Qed.

Lemma svd_f_rsub m n p (A : 'M[C]_(m,n+p)) i :
  svd_f (rsubmx A) i <= svd_f A i.
Proof. by rewrite -{2}[A]hsubmxK svd_f_row_mxr. Qed.

Lemma adjmx_unitary_cond m n (U : 'M[C]_(m,n)) :
  m = n -> U^*t \is unitarymx = (U \is unitarymx).
Proof. by move=>Pmn; case: _ / Pmn U; apply adjmx_unitary. Qed.

Lemma svd_f_mulmxUlr m n k (A : 'M[C]_(m,n)) (V : 'M[C]_(k,m)) (W : 'M[C]_(k,n)) i:
  V \is unitarymx -> W \is unitarymx ->
    svd_f (V *m A *m W^*t) i <= svd_f A i.
Proof.
move=>PV PW; rewrite (unitary_ext PV) (unitary_ext PW) 
  mul_usub_mx adjmxE trmx_usub map_lsubmx -adjmxE mul_usub_mx mulmx_lsub.
apply/(le_trans (svd_f_usub _ _))/(le_trans (svd_f_lsub _ _)).
move: PV PW => /unitary_dim PV /unitary_dim PW.
by rewrite svd_f_Ur_cond ?adjmx_unitary_cond ?svd_f_Ul_cond// ?schmidt_unitarymx// subnKC.
Qed.

(* to replace the detM in matrix.v (more general) *)
Lemma detM [R : comRingType] [n : nat] (A B : 'M[R]_n) :
  \det (A *m B) = \det A * \det B.
Proof. by case: n A B=>[A B|n A B]; rewrite ?detM// !det_mx00 mulr1. Qed.

Lemma det_unitary m (U : 'M[C]_m) : U \is unitarymx -> `| \det U | = 1.
Proof.
move=>/unitarymxPV /(f_equal determinant)/eqP.
by rewrite det1 detM det_map_mx det_tr -normCKC sqrp_eq1// =>/eqP.
Qed.

Lemma det_svds m (A : 'M[C]_m) :
  `| \det A | = \prod_i svds_d A 0 i.
Proof.
rewrite {1}(svdsE A) detM detM !normrM det_unitary// det_diag det_unitary//.
by rewrite mulr1 mul1r ger0_norm// prodr_ge0.
Qed.

Lemma det_svd_f m (A : 'M[C]_m) :
  `| \det A | = \prod_(i < m) svd_f A i.
Proof. by rewrite det_svds; apply eq_bigr=>i _; rewrite svds_dE. Qed.

Lemma det_mulmxUlr m n k (A : 'M[C]_(m,n)) (V : 'M[C]_(k,m)) (W : 'M[C]_(k,n)) :
  V \is unitarymx -> W \is unitarymx ->
    `|\det (V *m A *m W^*t)| <= \prod_(i < k) svd_f A i.
Proof.
move=>PV PW; rewrite det_svd_f ler_prod//==> i _.
by apply/andP; split=>//; apply/svd_f_mulmxUlr.
Qed.

Lemma cast_ord_sym m n (eqmn : m = n) i j :
  cast_ord eqmn i = j -> i = cast_ord (esym eqmn) j.
Proof. by case: n / eqmn j => j; rewrite !cast_ord_id. Qed.

Theorem polar_PU m n (A : 'M[C]_(m,n)) :
  (m <= n)%N -> exists (P : 'M_m) (U : 'M_(m,n)), 
    P \is psdmx /\ P *m P = A *m A^*t /\ U \is unitarymx /\ A = P *m U.
Proof.
move=>Pmn; exists (svd_u A *m diag_mx (svd_d_exdl (svd_d A)) *m (svd_u A)^*t).
exists (svd_u A *m (lsubmx (castmx (erefl, esym (subnKC Pmn)) (svd_v A)))^*t).
do ! split.
- by apply/psdmx_bimap_closed_gen/diagmx_nnegmx_psd/nnegmxP=>??; rewrite svd_d_exdlE.
- rewrite {7 8}[A]svdE !adjmxM adjmxK !mulmxA !mulmxKtV//; f_equal.
  rewrite -!mulmxA diag_mx_dmul cdiag_mx_mull; do ! f_equal; 
  by apply/matrixP=>??; rewrite mxE conj_Creal// ger0_real.
- apply/unitarymxP; rewrite -!adjmxE adjmxM !mulmxA mulmxACA 
  adjmxK adjmxE trmx_lsub map_usubmx -adjmxE mul_usub_mx mulmx_lsub 
    castmx_funE/= castmx_mul unitarymxKV//.
  set t := usubmx _; have -> : t = 1%:M.
    by apply/matrixP=>i j; rewrite !mxE castmxE/= mxE 
      (inj_eq (@cast_ord_inj _ _ _)) (inj_eq (@lshift_inj _ _)).
  by rewrite mulmx1 unitarymxK.
- rewrite mulmxA mulmxKtV// {1}[A]svdE -!mulmxA; f_equal.
  rewrite !adjmxE trmx_lsub map_usubmx trmx_cast/= map_castmx -adjmxE.
  rewrite mulmxUC// -mulmxA mul_usub_mx castmx_mull unitarymxKV//.
  apply/matrixP=>i j; rewrite mul_diag_mx !mxE !castmxE/= ord1 cast_ord_id esymK.
  rewrite !mxE; case: split_ordP=>k /cast_ord_sym ->;
  rewrite !mxE; case: split_ordP=>l /cast_ord_sym ->; rewrite !mxE ?mul0r//.
    by rewrite -[LHS]mulr_natr.
  case: eqP; last by rewrite mulr0.
  by move=>/(f_equal val)/= Pk; move: (ltn_ord k); rewrite Pk -ltn_subRL subnn.
Qed.

Theorem polar_UP m n (A : 'M[C]_(m,n)) :
  (n <= m)%N -> exists (P : 'M_n) (U : 'M_(m,n)), 
    P \is psdmx /\ P *m P = A^*t *m A /\ U^*t \is unitarymx /\ A = U *m P.
Proof.
move=>Pnm; move: (polar_PU A^*t Pnm)=>[P][U][P1][P2][P3]P4.
exists (P^*t); exists (U^*t); do ! split.
- by rewrite psdmx_adj.
- by rewrite -adjmxM P2 adjmxM !adjmxK.
- by rewrite adjmxK.
- by rewrite -adjmxM -P4 adjmxK.
Qed.

Theorem polar_PU_UQ m (A : 'M[C]_m) :
  exists (P Q : 'M_m) (U : 'M_m), 
    P \is psdmx /\ Q \is psdmx /\ P *m P = A *m A^*t /\ Q *m Q = A^*t *m A 
      /\ U \is unitarymx /\ A = P *m U /\ A = U *m Q.
Proof.
exists (svd_u A *m diag_mx (svds_d A) *m (svd_u A)^*t).
exists (svd_v A *m diag_mx (svds_d A) *m (svd_v A)^*t).
exists (svd_u A *m (svd_v A)^*t).
do ! split.
1,2: apply/psdmx_bimap_closed_gen/diagmx_nnegmx_psd/nnegmxP=>??; apply/svds_d_nneg.
1,2: rewrite [in RHS](svdsE A) !adjmxM !adjmxK !mulmxA !diag_mx_adj 
  !mulmxKtV// !mulmxACA !diag_mx_dmul; do ! f_equal;
  by apply/matrixP=>i j; rewrite !mxE conj_Creal ?ger0_real.
- by apply/unitarymx_mulmx_closed.
all: by rewrite ?adjmxM !mulmxA ?mulmxKtV// [LHS]svdsE.
Qed.

Lemma svd_f_form m n (A : 'M[C]_(m,n)) i :
  svd_f (A *m A^*t) i = (svd_f A i) ^+ 2.
Proof.
rewrite {1 2}[A]svdE !adjmxM adjmxK !mulmxA mulmxKtV// 
  mulmxACA cdiag_mx_mull svd_f_Ur// svd_f_Ul//.
have [Pi | Pi] := leqP m i.
  by rewrite !svd_f_eq0 ?(leq_trans (rank_leq_row _))// expr0n.
rewrite (svds_dEV _ (Ordinal Pi)) svds_diagmx svd_d_exdl_conj.
  apply/svd_diagP=>j; split=>[|k Pk]; rewrite !mxE -!normCK ?exprn_ge0//;
  by rewrite ler_pXn2r// ?nnegrE// !svd_d_exdlE !ger0_norm// svd_f_nincr.
by rewrite !mxE svd_d_exdlE/= -normCK ger0_norm.
Qed.

Lemma svd_f_formV m n (A : 'M[C]_(m,n)) i :
  svd_f (A^*t *m A) i = (svd_f A i) ^+ 2.
Proof. by rewrite -{2}[A]adjmxK svd_f_form svd_f_adjmx. Qed.

Theorem svd_f_prodM m n p (A : 'M[C]_(m,n)) (B : 'M[C]_(n,p)) k :
  \prod_(i < k) svd_f (A *m B) i <= \prod_(i < k) (svd_f A i * svd_f B i).
Proof.
have [Pk|Pk] := leqP k (minn m p); last first.
  by rewrite (bigD1 (Ordinal Pk))//= svd_f_eq0 ?rank_leq_min// 
    mul0r prodr_ge0// =>i _; rewrite mulr_ge0.
have cm : (k <= m)%N by apply/(leq_trans Pk)/geq_minl.
have cp : (k <= p)%N by apply/(leq_trans Pk)/geq_minr.
have [cn | Pn] := leqP k n; last first.
  rewrite (bigD1 (Ordinal Pn))//= svd_f_eq0 ?mulmx_max_rank// mul0r.
  by apply prodr_ge0=>? _; rewrite mulr_ge0.
pose Wk := \matrix_(i < k, j < p) (svd_v (A *m B))^*t (widen_ord cp i) j.
have Wk_row i : row i Wk = row (widen_ord cp i) (svd_v (A *m B))^*t.
  by apply/matrixP=>a b; rewrite !mxE.
pose Vk := \matrix_(i < k, j < m) (svd_u (A *m B))^*t (widen_ord cm i) j.
have Vk_row i : row i Vk = row (widen_ord cm i) (svd_u (A *m B))^*t.
  by apply/matrixP=>a b; rewrite !mxE.
move: (svd_u_unitarymx (A *m B)); rewrite -adjmx_unitary=>/row_unitarymxP PU.
move: (svd_v_unitarymx (A *m B)); rewrite -adjmx_unitary=>/row_unitarymxP PV.
have -> : \prod_(i < k) svd_f (A *m B) i = `| \det (Vk *m (A *m B) *m Wk^*t) |.
  have -> : (Vk *m (A *m B) *m Wk^*t) = diag_mx (\row_(i < k) svd_d (A *m B) 0 (widen_ord Pk i)).
    apply/matrixP=>i j.
    rewrite {1}(svdE (A *m B)) -!mulmxA -adjmxM mulmxA mxE 
      (bigD1 (widen_ord cm i))//= big1=>[l /negPf Pl|];
    rewrite -[svd_u _]adjmxK dot_dotmxE Vk_row PU ?eqxx 1?eq_sym ?Pl ?mul0r//.
    rewrite mul1r addr0 mxE (bigD1 (widen_ord cp j))//= big1=>[l /negPf Pl|];
    rewrite 2!mxE -[svd_v _]adjmxK dot_dotmxE Wk_row PV ?eqxx 1?eq_sym ?Pl ?conjC0 ?mulr0//.
    rewrite conjC1 addr0 mulr1 !mxE castmxE/=.
    set t := cast_ord _ _; have -> : t = lshift _ (widen_ord Pk i) by apply/val_inj.
    set s := cast_ord _ _; have -> : s = lshift _ (widen_ord Pk j) by apply/val_inj.
    by rewrite block_mxEul mxE (inj_eq (widen_ord_inj)).
  rewrite det_diag ger0_norm ?prodr_ge0// =>[/= i _|]; first by rewrite mxE.
  by apply eq_bigr=>i _; rewrite mxE svd_dE.
rewrite mulmxA -mulmxA.
move: (polar_UP (B *m Wk^*t) cn)=>[P][U][P1][P2][P3]P4.
rewrite P4 mulmxA detM normrM big_split/= ler_pM//.
  rewrite -[U]adjmxK; apply/det_mulmxUlr=>//; apply/row_unitarymxP=>i j; 
  by rewrite !Vk_row PU (inj_eq widen_ord_inj).
rewrite -(ler_pXn2r (n := 2))// ?nnegrE// ?prodr_ge0//.
rewrite expr2 -normrM -detM P2 adjmxM adjmxK mulmxA mulmxACA.
apply/(le_trans (det_mulmxUlr _ _ _)).
1,2: by apply/row_unitarymxP=>i j; rewrite !Wk_row PV (inj_eq widen_ord_inj).
by rewrite -prodrXl; under eq_bigr do rewrite -svd_f_formV.
Qed.

End Courant_Fischer.