From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.classical Require Import boolp cardinality mathcomp_extra
  classical_sets functions.
From mathcomp.analysis Require Import ereal reals signed topology 
  prodnormedzmodule normedtype sequences.
From mathcomp.analysis Require Import -(notations)forms.
(* From mathcomp.real_closed Require Import complex. *)
(* From quantum.external Require Import complex. *)
Require Import mcextra mcaextra notation mxpred.

(******************************************************************************)
(*           Modules and theories for both real and complex numbers           *)
(* -------------------------------------------------------------------------- *)
(* We formulate the extNumType R (where R is a real type) to capture the      *)
(* common properties of real and complex numbers.                             *)
(*         extNumType R == interface type that modes both R and R[i], i.e.,   *)
(*                         both R and R[i] are instances of extNumType R.     *)
(*                         The HB class is ExtNum.                            *)
(*             r2c, c2r := continuous mapping from R to C and from C to R     *)
(*                         that are bijective, r2c is also a rmorphsim        *)
(* -------------------------------------------------------------------------- *)
(*       finNormedModType C == interface type for a finite-dimensional normed *)
(*                             module structure over the numDomainType C      *)
(*                             join of NormedModule and Vector                *)
(*                             The HB class is FinNormedModule                *)
(* vorderFinNormedModType C == interface type for finNormedModule equipped    *)
(*                             with a closed vector orders over               *)
(*                             numFieldType C. It models the finite-          *)
(*                             dimensional ordered topological vector space   *)
(* -------------------------------------------------------------------------- *)
(* Theory of matrix over extNumType                                           *)
(*        vector norm are equivalent                                          *)
(*        Bolzano_Weierstrass theorem                                         *)
(*        Monotone convergence theorem (w.r.t. closed vorder)                 *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order Order.Theory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.
Import VNorm.Exports VOrder.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

HB.instance Definition _ (C : numDomainType) (V : normedModType C) := 
  isVNorm.Build C V (@normr C V) (@ler_normD C V) (@normr0_eq0 C V) (@normrZ C V).

Section closed_eq.

Lemma closed1 (T : topologicalType) : hausdorff_space T -> 
  forall t : T, closed [set t].
Proof. by move=>HT t; apply: compact_closed=>//; apply: compact_set1. Qed.

Lemma closed_eq (R : numFieldType) (V : pseudoMetricNormedZmodType R) (v : V) :
  closed [set x | x = v].
Proof. by apply: closed1; apply: norm_hausdorff. Qed.

End closed_eq.

Lemma lim_eq_near {T : Type} (V : topologicalType) 
  {F : set_system T} {FF : ProperFilter F} (u v : T -> V) : 
    hausdorff_space V ->
    (\forall n \near F, u n = v n) -> lim (u @ F) = lim (v @ F).
Proof.
move=>hV; move: (EM (cvg (u @ F)))=>[]; last first.
move=>divu eqn; rewrite (dvgP divu).
have eq1 : \near F, v F = u F by near=>x; symmetry; near: x.
suff: ~ cvg (v @ F) by move=>/dvgP->.
move: divu; apply/contra_not=>c. apply/(cvgP (lim (v @ F))).
move: eq1=>/near_eq_cvg d. apply: (cvg_trans d c).
by move=>c ?; apply/esym/(cvg_lim hV)/(cvg_trans _ c)/near_eq_cvg.
Unshelve. end_near.
Qed.

Lemma lim_eq {T: Type} {V : topologicalType} {F : set_system T} (u v : T -> V) :
  u =1 v -> lim (u @ F) = lim (v @ F).
Proof. by move=>/funext->. Qed.

Section TrivialMatrixFun.
Implicit Type (R: ringType).

Lemma mxf_dim0n R T p : all_equal_to ((fun=>0) : T -> 'M[R]_(0,p)).
Proof. by move=>h/=; apply/funext=>i; rewrite mx_dim0E. Qed.
Lemma mxf_dimn0 R T p : all_equal_to ((fun=>0) : T -> 'M[R]_(p,0)).
Proof. by move=>h/=; apply/funext=>i; rewrite mx_dim0E. Qed.

Lemma vec_mx_dim0n R m : @vec_mx R 0 m = fun=>0.
Proof. by apply/funext=>x; rewrite mx_dim0E. Qed.
Lemma vec_mx_dimn0 R m : @vec_mx R m 0 = fun=>0.
Proof. by apply/funext=>x; rewrite mx_dim0E. Qed.

Definition mx_dim0 := (mx_dim0n,mx_dimn0,mxf_dim0n,
  mxf_dimn0).

Lemma mx_dim0_cond R m n : (m == 0%N) || (n == 0%N) -> 
  all_equal_to (0 : 'M[R]_(m,n)).
Proof.
move=>/orP[/eqP/esym|/eqP/esym] P.
case: m / P; exact: mx_dim0n. case: n / P; exact: mx_dimn0.
Qed.

Lemma mxf_dim0_cond R m n T : (m == 0%N) || (n == 0%N) -> 
  all_equal_to ((fun=>0) : T -> 'M[R]_(m,n)).
Proof.
move=>/orP[/eqP/esym|/eqP/esym] P.
case: m / P; exact: mxf_dim0n. case: n / P; exact: mxf_dimn0.
Qed.
Definition mx_dim0C := (mx_dim0_cond, mxf_dim0_cond).

Variable (C : numFieldType) (p : nat).
Lemma mxcvgn_dim0n (h: nat -> 'M[C]_(0,p)) (x : 'M[C]_(0,p)) : h @ \oo --> x.
Proof. by rewrite !mx_dim0; apply: cvg_cst. Qed.
Lemma mxcvgn_dimn0 (h: nat -> 'M[C]_(p,0)) (x : 'M[C]_(p,0)) : h @ \oo --> x.
Proof. by rewrite !mx_dim0; apply: cvg_cst. Qed.
Lemma is_mxcvgn_dim0n (h: nat -> 'M[C]_(0,p)) : cvgn h.
Proof. by apply/cvg_ex; exists 0; apply mxcvgn_dim0n. Qed.
Lemma is_mxcvgn_dimn0 (h: nat -> 'M[C]_(p,0)) : cvgn h.
Proof. by apply/cvg_ex; exists 0; apply mxcvgn_dimn0. Qed.

End TrivialMatrixFun.

Section mx_norm_vnorm.

Lemma mx_normvZ (K: numDomainType) (m n: nat) (l : K) (x : 'M[K]_(m,n)) : 
  mx_norm (l *: x) = `| l | * mx_norm x.
Proof.
rewrite /= !mx_normE (eq_bigr (fun i => (`|l| * `|x i.1 i.2|)%:nng)); last first.
  by move=> i _; rewrite mxE //=; apply/eqP; rewrite -num_eq /= Num.Theory.normrM.
elim/big_ind2 : _ => // [|a b c d bE dE]; first by rewrite mulr0.
by rewrite !num_max bE dE Num.Theory.maxr_pMr.
Qed.

HB.instance Definition mx_norm_vnorm_mixin (K: numDomainType) (m n: nat) :=
  isVNorm.Build K 'M[K]_(m,n) (@mx_norm K m n)
    (@ler_mx_norm_add _ _ _) (@mx_norm_eq0 _ _ _) (@mx_normvZ K m n).
Definition mx_norm_vnorm (K: numDomainType) (m n: nat) :=
  (VNorm.Pack (VNorm.Class (mx_norm_vnorm_mixin K m n))).

HB.instance Definition _ (R : numDomainType) (V : normedModType R) :=
  isVNorm.Build R V _ (@Num.Theory.ler_normD _ V) (@Num.Theory.normr0_eq0 _ V) (@normrZ _ V).

Lemma mx_normEV (K: numDomainType) p q : 
  (@mx_norm _ _ _ : 'M[K]_(p.+1,q.+1) -> K) = (@Num.Def.normr _ _).
Proof. by apply/funext. Qed.

Lemma ball_dim0 (K: numFieldType) m n (x : 'M[K]_(m,n)) e y : 
  (m == 0%N) || (n == 0%N) -> ball x e y.
Proof.
move=>/orP[/eqP/esym Pm|/eqP/esym Pn]. 
case: m / Pm x y=>x y. 2: case: n / Pn x y=>x y.
1,2: by rewrite /ball/=/mx_ball=>i j; case: i=>//; case: j.
Qed.

Lemma mxball_normE (K: numFieldType) m n (x : 'M[K]_(m,n)) e y : 
  ball x e y <-> (m == 0%N) || (n == 0%N) || (mx_norm (x-y) < e).
case: m x y=>[x/= y|]; last case: n=>[m x/= y|n m x y/=].
1,2: by split=>// _; apply/ball_dim0.
by rewrite -ball_normE/=.
Qed.

Lemma cst_continuous_eq {T U : topologicalType} (f : T -> U) :
  (exists x : U, f = (fun=>x) ) -> continuous f.
Proof. move=>[x ->] y; apply: cst_continuous. Qed.

Lemma row_mx_norm (T : numDomainType) p m n 
  (M1 : 'M[T]_(p.+1,m.+1)) (M2 : 'M[T]_(p.+1,n.+1)) :
    mx_norm (row_mx M1 M2) = maxr (mx_norm M1) (mx_norm M2).
Proof.
rewrite /mx_norm; apply/le_anti/andP; split.
rewrite (bigmax_eq_arg _ (ord0,ord0))// =>[|i _]; last by rewrite -num_le//=.
set i := [arg max_(i > (ord0, ord0))`|row_mx M1 M2 i.1 i.2|%:nng]%O : 'I_p.+1 * 'I_(m.+1 + n.+1).
case: i=>a b/=; rewrite -(splitK b); case: (fintype.split b)=>/= c;
rewrite ?row_mxEl ?row_mxEr num_le_maxr; apply/orP; [left|right];
rewrite -num_abs_le//; apply/bigmax_geP; right;
by exists (a,c)=>//=; rewrite -num_le/= normr_id.
rewrite num_le_maxl; apply/andP; split;
rewrite (bigmax_eq_arg _ (ord0,ord0))// =>[|i _].
2,4: by rewrite -num_le//=. all: rewrite -num_abs_le//.
set i := [arg max_(i > (ord0, ord0))`|M1 i.1 i.2|%:nng]%O.
have: `|(`|M1 i.1 i.2|%:nng)%:num|%:nng <= `|row_mx M1 M2 
  (i.1,lshift n.+1 i.2).1 (i.1,lshift _ i.2).2|%:nng
  by rewrite/= row_mxEl -num_le/= normr_id.
by apply/bigmax_sup.
set i := [arg max_(i > (ord0, ord0))`|M2 i.1 i.2|%:nng]%O.
have: `|(`|M2 i.1 i.2|%:nng)%:num|%:nng <= `|row_mx M1 M2 
  (i.1,rshift m.+1 i.2).1 (i.1,rshift _ i.2).2|%:nng
  by rewrite/= row_mxEr -num_le/= normr_id.
by apply/bigmax_sup.
Qed.

Lemma mx_norm11 (T : numDomainType) (M : 'M[T]_1) :
  `|M| = `|M ord0 ord0|.
Proof.
rewrite {1}/normr/= mx_normE.
set i0 := (ord0,ord0) : 'I_1 * 'I_1.
have ->: \big[maxr/0%:nng]_i `|M i.1 i.2|%:nng = 
  maxr `|M i0.1 i0.2|%:nng 0%:nng.
  by apply: big_card1E; rewrite card_prod card_ord mul1n.
by rewrite max_l -?num_le//=.
Qed.

Lemma mxnorm_le_alter (T : numDomainType) m n (x : 'M[T]_(m.+1,n.+1))
  (y : T) : `|x| <= y <-> forall i, `|x i.1 i.2| <= y.
Proof.
case E: (y >= 0).
have -> : y = (NngNum E)%:num by [].
rewrite -mx_normEV /mx_norm; split; last first.
move=>H. rewrite num_le; apply/bigmax_leP=>/=; split.
by rewrite -num_le/=. by move=>i _; move: (H i); rewrite -num_le.
by rewrite num_le=>/bigmax_leP[] _ H i; move: (H i); rewrite -num_le/==>P; apply P.
split=>H. by move: (le_trans (normr_ge0 _) H); rewrite E.
move: (H (ord0,ord0))=>/= H1. by move: (le_trans (normr_ge0 _) H1); rewrite E.
Qed.

End mx_norm_vnorm.
Global Arguments mx_norm_vnorm {K m n}.

Section mxvec_norm.
Variable (R: numDomainType) (m n : nat).
Local Notation M := 'M[R]_(m,n).

Lemma mxvec_norm (x : M) : mx_norm x = mx_norm (mxvec x).
Proof.
case: m x=>[x|]; last case: n=>[m' x|n' m' x].
1,2: by rewrite !mx_dim0 ?linear0 !mx_norm0.
apply/le_anti/andP; split; rewrite /normr/=/mx_norm;
rewrite (bigmax_eq_arg _ (ord0, ord0))// ?ord1 ?num_le.
2,4: by move=>i _; rewrite/= -num_le/=.
by rewrite -mxvecE; apply: (le_trans _ (@le_bigmax_cond _ _ _ _ 
  (ord0,(mxvec_index [arg max_(i > (ord0, ord0))`|x i.1 i.2|%:nng]%O.1
  [arg max_(i > (ord0, ord0))`|x i.1 i.2|%:nng]%O.2)) _ _ _)).
set k := [arg max_(i > (ord0, ord0))`|mxvec x i.1 i.2|%:nng]%O.2 : 'I_(m'.+1*n'.+1).
case/mxvec_indexP: k => i j /=; rewrite (mxvecE x i j).
by apply: (le_trans _ (@le_bigmax_cond _ _ _ _ (i,j) _ _ _)).
Qed.

Lemma mxvec_normV x : mx_norm (vec_mx x : M) = mx_norm x.
Proof. by rewrite -{2}(vec_mxK x) mxvec_norm. Qed.

Lemma mx_normrE (x : 'M[R]_(m,n)) :
  mx_norm x = \big[maxr/0]_ij `| x ij.1 ij.2|.
Proof.
rewrite /mx_norm; apply/esym.
elim/big_ind2 : _ => //= a a' b b' ->{a'} ->{b'}.
case: (leP a b) => ab; by [rewrite max_r | rewrite max_l // ltW].
Qed.

Lemma mx_set_trivial (x : set M) :
  (m == 0%N) || (n == 0%N) -> x = set0 \/ x = setT.
Proof.
move=>/orP[/eqP/esym P1|/eqP/esym P1].
case: m / P1 x=>x. 2: case: n / P1 x=>x.
all: move: (EM (x 0))=>[]Px; [right|left];
by rewrite predeqE=>y; rewrite mx_dim0/=.
Qed.

Lemma mx_setT_trivial (x : M) :
  (m == 0%N) || (n == 0%N) -> [set x] = setT.
Proof.
move=>/orP[/eqP/esym P1|/eqP/esym P1].
case: m / P1 x=>x. 2: case: n / P1 x=>x.
all: by rewrite predeqE=>y; rewrite !mx_dim0/=.
Qed.

Lemma mx_set_trivial1 (x : set M) :
  (m == 0%N) || (n == 0%N) -> x = set0 \/ x = [set 0].
Proof.
move=>H; move: (mx_set_trivial x H)=>[]; [left|right]=>//.
by rewrite b mx_setT_trivial.
Qed.

End mxvec_norm.

(* show that mx norms are equivalent *)
Section mxvec_continuous.
Variable (R : numFieldType) (m n : nat).

Lemma vec_mx_continuous : continuous (@vec_mx R m n).
Proof.
move=> x s/= /nbhs_ballP [/=e egt0 Pb]; apply/nbhs_ballP.
exists e =>//=; move=> y /= Pxy.
apply (Pb (vec_mx y)); move: Pxy; clear Pb.
case: m x s y=>[x _ y _|]; last case: n=>[m' x _ y _|n' m' x s y].
1,2: by apply: ball_dim0; rewrite eqxx.
by rewrite -!ball_normE/= -linearB/= -!mx_normEV mxvec_normV.
Qed.

Lemma mxvec_continuous : continuous (@mxvec R m n).
Proof.
move=> x s/= /nbhs_ballP [/=e egt0 Pb];
apply/nbhs_ballP; exists e =>//=;
move=> y /= Pxy; apply (Pb (mxvec y)); move: Pxy; clear Pb.
case: m x s y=>[x _ y _|]; last case: n=>[m' x _ y _|n' m' x s y].
1,2: by apply: ball_dim0; rewrite ?muln0 ?mul0n eqxx.
by rewrite -!ball_normE/= -{1}(mxvecK x) -{1}(mxvecK y) 
  -linearB/= -!mx_normEV mxvec_normV.
Qed.

Lemma mxvec_open_set (A: set 'M[R]_(m,n)) :
  open A <-> open (mxvec @` A).
Proof.
rewrite !openE; split=>/=.
move=>P1 y/= [x Px eqxy]; move: (P1 x Px) =>/=; rewrite /interior.
move/nbhs_ballP=>[/=e egt0 Pb]; apply/nbhs_ballP.
exists e=>// z/= Pz; exists (vec_mx z); last by rewrite vec_mxK.
by apply Pb; move: Pz; rewrite !mxball_normE/= muln_eq0 
  -(mxvecK x) -linearB/= mxvec_normV eqxy.
move=>P1 y/= Py. 
have P3: (exists2 x : 'M_(m, n), A x & mxvec x = mxvec y) by exists y.
move: (P1 (mxvec y) P3); rewrite /interior.
move/nbhs_ballP=>[/=e egt0 Pb]; apply/nbhs_ballP.
exists e=>// z/= Pz; move: Pz (Pb (mxvec z)).
rewrite !mxball_normE/= muln_eq0 -linearB/= mxvec_norm=>P4 P5.
by move: (P5 P4)=>[t Pt] /eqP; rewrite (inj_eq (can_inj mxvecK))=>/eqP <-.
Qed.

Lemma mxvec_setN (A: set 'M[R]_(m,n)) : 
  ~` [set mxvec x | x in A] = [set mxvec x | x in ~` A].
Proof.
rewrite seteqP; split=>x/=; rewrite -forall2NP.
move=>/(_ (vec_mx x)); rewrite vec_mxK =>[[|//]].
by exists (vec_mx x)=>//; rewrite vec_mxK.
move=>[y Py eqxy] z; case E: (y == z).
left; by move/eqP: E=><-.
by right; rewrite -eqxy=>/eqP; rewrite (inj_eq (can_inj mxvecK)) eq_sym E.
Qed.

Lemma mxvec_closed_set (A: set 'M[R]_(m,n)) :
  closed A <-> closed (mxvec @` A).
Proof.
split. by rewrite -openC mxvec_open_set -closedC -{2}(setCK A) -mxvec_setN.
by rewrite -openC mxvec_setN -mxvec_open_set -closedC setCK.
Qed.

Lemma mx_set_compact_trivial (x : set 'M[R]_(m,n)) :
  (m == 0%N) || (n == 0%N) -> compact x.
Proof.
move=>/(mx_set_trivial1 x)[->|->]. apply: compact0. apply: compact_set1.
Qed.

Lemma mx_set_closed_trivial (x : set 'M[R]_(m,n)) :
  (m == 0%N) || (n == 0%N) -> closed x.
Proof.
move=>/(mx_set_trivial x)[->|->]. apply: closed0. apply: closedT.
Qed.

Lemma mx_set_open_trivial (x : set 'M[R]_(m,n)) :
  (m == 0%N) || (n == 0%N) -> open x.
Proof.
move=>/(mx_set_trivial x)[->|->]. apply: open0. apply: openT.
Qed.

End mxvec_continuous.

Lemma normv_snum_subproof (R : numDomainType) (V : lmodType R) (nv : vnorm V) 
  (x : V) : Signed.spec 0 ?=0 >=0 (nv x).
Proof. by rewrite /= normv_ge0. Qed.

Canonical normv_snum (R : numDomainType) (V : lmodType R) (nv : vnorm V) 
  (x : V) := Signed.mk (normv_snum_subproof nv x).

(* non-degenerated, at least 1*1 dim *)
Section MxNormFieldND.
Variable (R: numFieldType) (m n : nat).
Local Notation M := 'M[R]_(m.+1,n.+1).
Variable (mnorm : vnorm M).

Let mnorm_max := (\big[maxr/0%:nng]_i (mnorm (delta_mx i.1 i.2))%:nng)%:num.
Let mnorm_elem i := ((mnorm (delta_mx i.1 i.2))%:nng)%:num.
Let mxnorm_elem (x : M) i j := (`|x i j|%:nng)%:num.
Let R0 := (0 : R)%:nng%:num.

Lemma mnorm_ubounded_ND : exists2 c : R, 0 < c & forall x, mnorm x <= c * `|x|.
Proof.
exists ((m.+1 * n.+1)%:R * mnorm_max); last first.
move=>x; rewrite {1}(matrix_sum_delta x) pair_big/=.
apply: (le_trans (normv_sum _ _ _)).
have <-: \sum_(i: 'I_m.+1 * 'I_n.+1) (mnorm_max * `|x|) = (m.+1 * n.+1)%:R * mnorm_max * `|x|.
by rewrite sumr_const card_prod !card_ord -mulr_natl mulrA.
apply: ler_sum=>/= i _; rewrite normvZ mulrC; apply ler_pM.
by apply normv_ge0. by apply normr_ge0.
suff: mnorm_elem i <= mnorm_max by [].
rewrite /mnorm_elem /mnorm_max num_le; by apply: le_bigmax_cond.
suff: mxnorm_elem x i.1 i.2 <= `|x|. by [].
rewrite /mxnorm_elem -mx_normEV mx_normE num_le.
by apply: le_bigmax_cond.
apply mulr_gt0. by rewrite ltr0n.
suff: R0 < mnorm_max. by [].
rewrite /mnorm_max /R0 num_lt. apply/bigmax_gtP. right.
exists (ord0, ord0)=>//=.
rewrite -num_lt/= lt_def normv_ge0 andbT.
have: (delta_mx ord0 ord0 != (0 : M)).
apply/negP=>/eqP/matrixP/(_ ord0 ord0). rewrite !mxE !eqxx/=.
move/eqP. apply/negP. by apply oner_neq0.
apply contraNN. by move/eqP/normv0_eq0=>->.
Qed.

Lemma open_mxnorm_gt (y : R) : open [set x : M | `|x| > y].
Proof.
move=> x /=; rewrite -subr_gt0 => xDy_gt0.
apply/nbhs_ballP; exists (`|x| - y) => // z.
rewrite -ball_normE/= ltrBrDl -ltrBrDr=>P.
apply (lt_le_trans P). rewrite -{1}(normrN x).
move: (lerB_normD (-x) (x-z)).
by rewrite addKr !normrN.
Qed.

Lemma open_mxnorm_lt (y : R) : open [set x : M | `|x| < y].
Proof.
move=> x /=; rewrite -subr_gt0 => xDy_gt0.
apply/nbhs_ballP; exists (y - `|x|) => // z.
rewrite -ball_normE/= ltrBrDl=>P.
apply: (le_lt_trans _ P).
move: (ler_normD (-x) (x-z)).
by rewrite addKr !normrN.
Qed.

Lemma closed_mxnorm_le (y : R) : closed [set x : M | `|x| <= y].
Proof.
case E: (y \is Num.real).
rewrite (_ : mkset _ = ~` [set x | `| x | > y]).
rewrite closedC. apply open_mxnorm_gt.
rewrite predeqE => x /=; split=>[|/negP].
move=>P1; apply/negP; move: P1.
1,2: by rewrite real_ltNge// negbK.
rewrite (_ : mkset _ = set0); first by apply: closed0.
rewrite predeqE => x /=; split=>[P1|//].
by move: (le_trans (normr_ge0 _) P1)=>/ger0_real; rewrite E.
Qed.

Lemma closed_mxnorm_sphere (y : R) : closed [set x : M | `|x| = y].
Proof.
case E: (y \is Num.real).
rewrite (_ : mkset _ = ~` [set x | `| x | > y] `&` ~` [set x | `| x | < y]).
apply closedI; rewrite closedC. apply open_mxnorm_gt. apply open_mxnorm_lt.
rewrite predeqE => x /=; split; first by move=>->; rewrite !ltxx.
move=>[/negP P1 /negP P2].
move: P1 P2; rewrite !real_ltNge ?real1// !negbK=>/le_gtF P1.
by rewrite le_eqVlt P1 orbF=>/eqP <-.
rewrite (_ : mkset _ = set0); first by apply: closed0.
rewrite predeqE => x /=; split=>[P1|//].
by move: E; rewrite -P1 ger0_real.
Qed.

Lemma continuous_mnorm_ND : continuous mnorm.
Proof.
move: mnorm_ubounded_ND => [c cgt0 mnormb].
move=> x s/= /nbhs_ballP [/=e egt0 Pb].
apply/nbhs_ballP. exists (e / c) =>//=; first by apply divr_gt0.
move=> y /= Pxy. apply (Pb (mnorm y)). move: Pxy. 
rewrite mx_norm_ball /ball /= => P1.
apply (le_lt_trans (lev_dist_dist x y)). 
apply (le_lt_trans (mnormb (x - y))).
by rewrite mulrC -ltr_pdivlMr.
Qed.

Let R1 := (1 : R)%:nng%:num.

Lemma mxnorm_sphere_neq0_vint : (mnorm @` [set x : M | `|x| = 1%:R]) !=set0.
Proof.
exists (mnorm (const_mx 1))=>/=. exists (const_mx 1)=>//.
have ->: 1%:R = R1 by [].
rewrite /normr/=/mx_norm.
apply/le_anti; apply/andP; split; rewrite /R1 num_le.
by apply/bigmax_leP; split=>[|i _]; rewrite -num_le/=// mxE normr1.
by apply/bigmax_geP=>/=; right; exists (ord0,ord0)=>//; rewrite -num_le/= mxE normr1.
Qed.
End MxNormFieldND.

(* we prove the property without assumption of non-degenerate *)
(* though this is trivial but with .+1 are difficult to use for e.g. vectType *)
Section MxNormFieldEqual.
Variable (R: numFieldType) (m n : nat).
Local Notation M := 'M[R]_(m,n).
Variable (mnorm : vnorm M).

Lemma mnorm_ubounded : exists2 c : R, 
  0 < c & forall x : M, mnorm x <= c * mx_norm x.
Proof.
case: m mnorm=>[mnorm'|m']; last case: n=>[mnorm'|n' mnorm'].
1,2: by exists 1=>// x; rewrite mx_dim0 !normv0 mul1r.
exact: mnorm_ubounded_ND.
Qed.

Let cu := projT1 (cid2 mnorm_ubounded).
Let cu_gt0 : cu > 0.
Proof. by move: (projT2 (cid2 mnorm_ubounded))=>[]. Qed.
Let cuP : forall x, mnorm x <= cu * mx_norm x.
Proof. by move: (projT2 (cid2 mnorm_ubounded))=>[]. Qed.
Let cuPV : forall x, mnorm x / cu <= mx_norm x.
Proof. by move=>x; rewrite ler_pdivrMr// mulrC. Qed.

Lemma open_mnorm_gt (y : R) : open [set x : M | mnorm x > y].
Proof.
move=> x /=; rewrite -subr_gt0 => xDy_gt0.
apply/nbhs_ballP. exists ((mnorm x - y)/cu)=>/=[]; first by rewrite divr_gt0.
move=>z/mxball_normE/orP[/orP[]/=P|].
1,2: by move: xDy_gt0; rewrite !mx_dim0C ?P// ?orbT// subr_gt0.
move=>P/=; move: (le_lt_trans (cuPV _) P).
rewrite ltr_pM2r ?invr_gt0// ltrBrDl addrC -ltrBrDl.
by move=>P1; move: (lt_le_trans P1 (levB_dist _ _)); rewrite subKr.
Qed.

Lemma open_mnorm_lt (y : R) : open [set x : M | mnorm x < y].
Proof.
move=> x /=; rewrite -subr_gt0 => xDy_gt0.
apply/nbhs_ballP. exists ((y - mnorm x)/cu)=>/=[]; first by rewrite divr_gt0.
move=>z/mxball_normE/orP[/orP[]/=P|].
1,2: by move: xDy_gt0; rewrite !mx_dim0C ?P// ?orbT// subr_gt0.
move=>P/=; move: (le_lt_trans (cuPV _) P).
rewrite ltr_pM2r ?invr_gt0// ltrBrDl.
by move=>P1; move: (le_lt_trans (lev_normB _ _) P1); rewrite subKr.
Qed.

Lemma closed_mnorm_le (y : R) : closed [set x : M | mnorm x <= y].
Proof.
case E: (y \is Num.real).
rewrite (_ : mkset _ = ~` [set x | mnorm x > y]).
rewrite closedC. apply open_mnorm_gt.
rewrite predeqE => x /=; split=>[|/negP].
move=>P1; apply/negP; move: P1.
1,2: by rewrite real_ltNge// negbK.
rewrite (_ : mkset _ = set0); first by apply: closed0.
rewrite predeqE => x /=; split=>[/ler_real|//].
by rewrite E normv_real.
Qed.

Lemma closed_mnorm_ge (y : R) : closed [set x : M | y <= mnorm x].
Proof.
case E: (y \is Num.real).
rewrite (_ : mkset _ = ~` [set x | mnorm x < y]).
rewrite closedC. apply open_mnorm_lt.
rewrite predeqE => x /=; split=>[|/negP].
move=>P1; apply/negP; move: P1.
1,2: by rewrite real_ltNge// negbK.
rewrite (_ : mkset _ = set0); first by apply: closed0.
rewrite predeqE => x /=; split=>[/ler_real|//].
by rewrite E normv_real.
Qed.

Lemma closed_mnorm_sphere (y : R) : closed [set x : M | mnorm x = y].
Proof.
case E: (y \is Num.real).
rewrite (_ : mkset _ = ~` [set x | mnorm x > y] `&` ~` [set x | mnorm x  < y]).
apply closedI; rewrite closedC. apply open_mnorm_gt. apply open_mnorm_lt.
rewrite predeqE => x /=; split; first by move=>->; rewrite !ltxx.
move=>[/negP P1 /negP P2].
move: P1 P2; rewrite !real_ltNge ?real1// !negbK=>/le_gtF P1.
by rewrite le_eqVlt P1 orbF=>/eqP <-.
rewrite (_ : mkset _ = set0); first by apply: closed0.
rewrite predeqE => x /=; split=>[P1|//].
by move: E; rewrite -P1 ger0_real.
Qed.

Lemma continuous_mnorm : continuous mnorm.
Proof.
case: m mnorm=>[mnorm'|m']; last case: n=>[mnorm'|n' mnorm']; last exact: continuous_mnorm_ND.
1,2:by apply: cst_continuous_eq; exists 0; apply/funext=>x; rewrite mx_dim0 normv0.
Qed.

Lemma mxcvgn_mnorm (f : M ^nat) (a: M) : 
  f @ \oo --> a -> (fun x=> mnorm (f x)) @ \oo --> (mnorm a).
Proof. by apply: continuous_cvg; apply: continuous_mnorm. Qed.

Lemma is_mxcvgn_mnorm (f : M ^nat) : cvgn f -> cvgn (mnorm \o f).
Proof. by have := cvgP _ (mxcvgn_mnorm _); apply. Qed.

End MxNormFieldEqual.

(* n-dim number : vectType R, f *)
(* general theory over extNum; R, R[i] are both extNum. *)

Module Aux.
Definition continuous (R : realType) (C : numFieldType) (c2r : C -> R) := continuous c2r.
Definition compact (C : numFieldType) (A : set C) := compact A.
End Aux.

HB.mixin Record NumField_isExtNum (R : realType) C of Num.NumField C:= {
  r2c : {rmorphism R -> C};
  c2r : C -> R;
  ler_r2c : {mono r2c : x y / x <= y};
  r2cK : cancel r2c c2r;
  c2rK : {in Num.real, cancel c2r r2c};
  Aux_c2r_continuous : Aux.continuous c2r;
  c2rP : forall (a : R) (b c : C), 
    c2r ((r2c a) * b + c) = a * (c2r b) + c2r c;
  Aux_extNum_bounded_compact :
    forall a : C, Aux.compact [set x : C | `|x| <= a];
  (* _ : closed [set x : C | 0 <=  x]; *)
}.

#[short(type="extNumType")]
HB.structure Definition ExtNum (R : realType) :=
  { C of Num.NumField C & NumField_isExtNum R C}.

Module ExtNumExports.
#[deprecated(since="mathcomp 2.0.0", note="Use ExtNum.clone instead.")]
Notation "[ 'extNumType' R 'of' T 'for' cT ]" := (ExtNum.clone R T%type cT)
  (at level 0, format "[ 'extNumType'  R  'of'  T  'for'  cT ]") : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use ExtNum.clone instead.")]
Notation "[ 'extNumType' R 'of' T ]" := (ExtNum.clone R T%type _)
  (at level 0, format "[ 'extNumType'  R  'of'  T ]") : form_scope.
End ExtNumExports.
HB.export ExtNumExports.

Module ExtNumTopology.
Import numFieldNormedType.Exports Num.Def Num.Theory.

Section ExtNumInternal.
Context {R: realType} {C : extNumType R}.

#[export, non_forgetful_inheritance]
HB.instance Definition _ := NormedModule.copy C [numFieldType of C].

Local Notation r2c := (@r2c R C).
Local Notation c2r := (@c2r R C).
Lemma r2c_inj : injective r2c. Proof. exact: (can_inj r2cK). Qed.
Lemma c2r_continuous : continuous c2r.
Proof. exact: Aux_c2r_continuous. Qed.
Lemma c2r_is_additive : additive c2r.
Proof. by move=>a b; rewrite -[in RHS]mulN1r [RHS]addrC -c2rP rmorphN1 mulN1r addrC. Qed.
HB.instance Definition _ := GRing.isAdditive.Build C R c2r c2r_is_additive.
Lemma r2c0 : r2c 0 = 0. Proof. exact: rmorph0. Qed.
Lemma r2c1 : r2c 1 = 1. Proof. by exact: rmorph1. Qed.
Lemma c2r0 : c2r 0 = 0. Proof. exact: raddf0. Qed.
Lemma c2r1 : c2r 1 = 1. Proof. by rewrite -[RHS](@r2cK R C) rmorph1. Qed.
Lemma c2rN : {morph c2r : u / -u}. Proof. exact: raddfN. Qed.
Lemma c2rB : {morph c2r : u v / u - v}. Proof. exact: raddfB. Qed.
Lemma c2rD : {morph c2r : u v / u + v}. Proof. exact: raddfD. Qed.
Lemma c2rMn n : {morph c2r : u / u *+ n}. Proof. exact: raddfMn. Qed.
Lemma c2rMNn n : {morph c2r : u / u *- n}. Proof. exact: raddfMNn. Qed.
Lemma c2rZ (a : R) (b : C) : c2r ((r2c a) * b) = a * c2r b.
Proof. by rewrite -[RHS]addr0 -c2r0 -c2rP addr0. Qed.

Lemma extNum_bounded_compact (a : C) : compact [set x : C | `|x| <= a].
Proof. exact: Aux_extNum_bounded_compact. Qed.

End ExtNumInternal.

Section ExtNumTheory.
Context {R: realType} {C : extNumType R}.

Lemma ltr_r2c : {mono @r2c R C : x y / x < y}.
Proof. by move=>x y; rewrite !lt_def ler_r2c (inj_eq r2c_inj). Qed.
Lemma r2c_ge0 x : (0 <= r2c x :> C) = (0 <= x).
Proof. by rewrite -(@ler_r2c _ C) rmorph0. Qed.
Lemma r2c_gt0 x : (0 < r2c x :> C) = (0 < x).
Proof. by rewrite -ltr_r2c rmorph0. Qed.
Lemma r2c_le0 x : (r2c x <= 0 :> C) = (x <= 0).
Proof. by rewrite -(@ler_r2c _ C) rmorph0. Qed.
Lemma r2c_lt0 x : (r2c x < 0 :> C) = (x < 0).
Proof. by rewrite -ltr_r2c rmorph0. Qed.

Lemma ler_c2r x y : x <= y -> @c2r _ C x <= c2r y.
Proof. by rewrite -subr_ge0=>H; rewrite -subr_ge0 -c2rB -r2c_ge0 c2rK// ger0_real. Qed.
Lemma ltr_c2r x y : x < y -> @c2r _ C x < c2r y.
Proof. by rewrite -subr_gt0=>H; rewrite -subr_gt0 -c2rB -r2c_gt0 c2rK// gtr0_real. Qed.
Lemma c2r_ge0 (x : C) : 0 <= x -> 0 <= c2r x.
Proof. by move=>H; rewrite -r2c_ge0 c2rK// ger0_real. Qed.
Lemma c2r_gt0 (x : C) : 0 < x -> 0 < c2r x.
Proof. by move=>H; rewrite -r2c_gt0 c2rK// gtr0_real. Qed.

Lemma r2c_real (r : R) : (r2c r : C) \is Num.real.
Proof. by rewrite realE r2c_ge0 r2c_le0 -realE num_real. Qed.

Lemma r2c_norm x : `|r2c x : C| = r2c `|x|.
Proof.
case E : (0 <= x); first by rewrite !ger0_norm// r2c_ge0.
move: E=>/negP/negP; rewrite -real_ltNge// ?num_real// =>Px.
by rewrite !ler0_norm ?rmorphN//; apply/ltW=>//; rewrite r2c_lt0.
Qed.

Lemma r2c_continuous : continuous (r2c : {rmorphism R -> C}).
Proof.
move=>x y/=; rewrite /nbhs/= /nbhs/==>[[]e/=egt0 P].
exists (c2r e)=>/=. by rewrite -ltr_r2c rmorph0 c2rK// gtr0_real.
move=>z/==>Pxz; apply: (P (r2c z)); rewrite/= -rmorphB r2c_norm.
by move: Pxz; rewrite -ltr_r2c c2rK// gtr0_real.
Qed.

Lemma extNum_compact_minmax (S : (set C)) : 
  S `<=` [set` Num.real] (* real *)
  -> compact S -> S !=set0 -> (* compact & non-empty *)
    (exists2 x, S x & (forall y, S y -> y <= x)) /\
    (exists2 x, S x & (forall y, S y -> x <= y)).
Proof.
move=>Sr Sc S0.
have SrE : S = r2c @` (c2r @` S).
rewrite predeqE=>x/=; split.
move=>Sx. exists (c2r x). by exists x. by rewrite c2rK//; apply Sr.
by move=>[y][z] Sz <- <-; rewrite c2rK//; apply Sr.
have S1 : compact (c2r @` S). apply/continuous_compact=>//. 
apply/continuous_subspaceT=>x ?. apply/c2r_continuous.
have S2: [set c2r x | x in S] !=set0.
by move: S0=>[x Px]; exists (c2r x)=>/=; exists x.
split.
move: (compact_max S1 S2)=>[x Px1 Px2].
2: move: (compact_min S1 S2)=>[x Px1 Px2].
all: move: Px1=>/=[y Py Py1]; exists y=>// z Pz.
all: move: (Px2 (c2r z))=>/==>P1.
all: rewrite -[z]c2rK; last by apply: Sr.
all: rewrite -[y]c2rK; last by apply: Sr.
all: by rewrite Py1 ler_r2c; apply P1; exists z.
Qed.

Lemma extNum_compact_max (S : (set C)) : 
  S `<=` [set` Num.real] (* real *)
  -> compact S -> S !=set0 -> (* compact & non-empty *)
    (exists2 x, S x & (forall y, S y -> y <= x)).
Proof. by move=>P1 P2 P3; move: (extNum_compact_minmax P1 P2 P3)=>[]. Qed.

Lemma extNum_compact_min (S : (set C)) : 
  S `<=` [set` Num.real] (* real *)
  -> compact S -> S !=set0 -> (* compact & non-empty *)
    (exists2 x, S x & (forall y, S y -> x <= y)).
Proof. by move=>P1 P2 P3; move: (extNum_compact_minmax P1 P2 P3)=>[]. Qed.

Lemma extNum_complete (F : set_system C) : ProperFilter F -> cauchy F -> cvg F.
Proof. apply: bounded_compact_complete. exact: extNum_bounded_compact. Qed.

HB.instance Definition _ := Uniform_isComplete.Build C (@extNum_complete).

Lemma ethausdorff : hausdorff_space C. Proof. apply: norm_hausdorff. Qed.

Lemma etclosed_real : closed [set x : C | x \is Num.real].
Proof.
rewrite closure_id closureEcvg predeqE=>x/=; split=>[xr|[G PG[] Gx] P].
  exists (at_point x); first by exact: at_point_filter.
  split; last by move=>a/=/(_ _ xr); rewrite/at_point.
  rewrite/cvg_to/==>t/=; rewrite {2}/nbhs/at_point/=.
  by move=>[e]/= egt0; rewrite/= ball_normE=>/(_ x)P; apply/P/ballxx.
have P1: c2r @ G --> c2r x 
  by apply: continuous_cvg=>//; apply: c2r_continuous.
suff P2: G `<=` r2c @ (c2r @ G).
  have P3: r2c @ (c2r @ G) --> x by apply: (subset_trans Gx P2).
  have P4: r2c @ (c2r @ G) --> (r2c (c2r x) : C).
    by apply: continuous_cvg=>//; apply: r2c_continuous.
  have: close x (r2c (c2r x)) by apply: (cvg_close P3 P4).
  by move=>/(close_eq ethausdorff)->; apply: r2c_real.
move=>a/=; rewrite/nbhs/=/nbhs/==>Ga.
have Gr: G [set` Num.real] by apply: P=>/=.
move: (@filterI _ _ PG _ _ Ga Gr).
apply: filterS=>t/=[] P5 P6; rewrite c2rK//.
Qed.

Lemma extNum_ltr_add_invr (y x : C) : y < x -> exists k, y + k.+1%:R^-1 < x.
Proof.
rewrite -subr_gt0=>P1.
have P2 : 0 < c2r (x - y) by rewrite -ltr_r2c c2rK ?rmorph0// gtr0_real.
by move: (ltr_add_invr P2)=>[k]; rewrite add0r -ltr_r2c c2rK ?gtr0_real// 
  fmorphV rmorphMn rmorph1 ltrBrDl=>P; exists k.
Qed.

Lemma extNum_archi (x : C) : 0 < x -> exists k, k.+1%:R^-1 < x.
Proof. by move=>/extNum_ltr_add_invr[k Pk]; exists k; rewrite add0r in Pk. Qed.

(* have convergence subsequence *)
Lemma extNum_bounded_subsvg (f : nat -> C) b : (forall i, `|f i| <= b) -> 
  exists (h: nat -> nat), (forall n, (h n.+1 > h n)%N) /\ cvgn (f \o h).
Proof.
move=>Pb; move: (@extNum_bounded_compact _ _ b)=>P1.
apply: (cluster_subsvg _ P1 _)=>[|i//=]; apply: extNum_archi.
Qed.

End ExtNumTheory.

Section matrix_CompleteNormedModule.
Variables (R: realType) (C : extNumType R).

Variables (m n: nat).

HB.instance Definition _ := CompleteNormedModule.Class
  (NormedModule.on 'M[C]_(m.+1, n.+1)) (Complete.on 'M[C]_(m.+1, n.+1)).

Definition extNumMx_cauchy_seq  m n (u: nat -> 'M[C]_(m,n)) := 
  forall e : C, 0 < e -> exists N : nat, 
    forall s t, (N <= s)%N -> (N <= t)%N -> mx_norm (u s - u t) < e.

End matrix_CompleteNormedModule.

Section ExtNumCvg.
Context {R: realType} {C: extNumType R}.
Context {T : Type} {F : set_system T} {FF : ProperFilter F}.
Implicit Type (f g: T -> C) (s a b : C).

Lemma etcvg_map f a (V : completeType) (h : C -> V) :
  continuous h -> f @ F --> a -> (h \o f) @ F --> h a.
Proof. 
move=>ch cvgf; apply: (@cvg_fmap _ _ (f @ F) a h).
by apply ch. by apply cvgf.
Qed.

Lemma is_etcvg_map f (V : completeType) (h : C -> V) :
  continuous h -> cvg (f @ F) -> cvg ((h \o f) @ F).
Proof.
move=>P1 /cvg_ex=>[/= [a Pa]]. apply/cvg_ex.
exists (h a). by move: (etcvg_map P1 Pa).
Qed.

Lemma etlim_map f (V : completeType) (h : C -> V) :
  hausdorff_space V -> continuous h -> 
    cvg (f @ F) -> lim ((h \o f) @ F) = h (lim (f @ F)).
Proof. by move=>hV ch; move/(etcvg_map ch)/cvg_lim=>/(_ hV). Qed.

Lemma etcvg_mapV (V : completeType) (h : V -> C) (h' : T -> V) (a : V) :
  continuous h -> h' @ F --> a -> (h \o h') @ F --> h a.
Proof. 
move=>ch cvgf; apply: (@cvg_fmap _ _ (h' @ F) a h).
by apply ch. by apply cvgf.
Qed.

Lemma is_etcvg_mapV (V : completeType) (h : V -> C) (h' : T -> V) :
  continuous h -> cvg (h' @ F) -> cvg ((h \o h') @ F).
Proof.
move=>P1 /cvg_ex=>[/= [a Pa]]. apply/cvg_ex.
exists (h a). by move: (etcvg_mapV P1 Pa).
Qed.

Lemma etlim_mapV (V : completeType) (h : V -> C) (h' : T -> V) :
  continuous h -> cvg (h' @ F) -> lim ((h \o h') @ F) = h (lim (h' @ F)).
Proof. by move=>ch; move/(etcvg_mapV ch)/cvg_lim=>/(_ ethausdorff). Qed.

End ExtNumCvg.

(* Section ExtNumCvg.
Context {R: realType} {C: extNumType R}.
Implicit Type (f g: nat -> C) (n: nat) (s a b : C).

Lemma etcvg_map f a (V : completeType) (h : C -> V) :
  continuous h -> f @ \oo --> a -> (h \o f) --> h a.
Proof. 
move=>ch cvgf; apply: (@cvg_fmap _ _ [filter of f] a h).
by apply ch. by apply cvgf.
Qed.

Lemma is_etcvg_map f (V : completeType) (h : C -> V) :
  continuous h -> cvg f -> cvg (h \o f).
Proof.
move=>P1 /cvg_ex=>[/= [a Pa]]. apply/cvg_ex.
exists (h a). by move: (etcvg_map P1 Pa).
Qed.

Lemma etlim_map f (V : completeType) (h : C -> V) :
  hausdorff_space V -> continuous h -> cvg f -> lim (h \o f) = h (lim f).
Proof. by move=>hV ch; move/(etcvg_map ch)/cvg_lim=>/(_ hV). Qed.

Lemma etcvg_mapV (V : completeType) (h : V -> C) (h' : nat -> V) (a : V) :
  continuous h -> h' --> a -> (h \o h') --> h a.
Proof. 
move=>ch cvgf; apply: (@cvg_fmap _ _ [filter of h'] a h).
by apply ch. by apply cvgf.
Qed.

Lemma is_etcvg_mapV (V : completeType) (h : V -> C) (h' : nat -> V) :
  continuous h -> cvg h' -> cvg (h \o h').
Proof.
move=>P1 /cvg_ex=>[/= [a Pa]]. apply/cvg_ex.
exists (h a). by move: (etcvg_mapV P1 Pa).
Qed.

Lemma etlim_mapV (V : completeType) (h : V -> C) (h' : nat -> V) :
  continuous h -> cvg h' -> lim (h \o h') = h (lim h').
Proof. by move=>ch; move/(etcvg_mapV ch)/cvg_lim=>/(_ ethausdorff). Qed.

End ExtNumCvg. *)

Section ExtNumMono.
Variable (R: realType) (C: extNumType R).

Lemma etclosed_ge (y:C) : closed [set x : C | y <= x].
Proof.
rewrite (_ : mkset _ = (fun x=>x-y) @^-1` ([set` Num.real] `&` c2r @^-1` [set x | 0 <= x ])).
apply: closed_comp=>[x _|]; first by apply: addl_continuous.
apply: closedI. apply/etclosed_real. apply: closed_comp=>[x _|].
apply: c2r_continuous. apply/closed_ge.
rewrite predeqE=>x; rewrite/= -[y <= x]subr_ge0; split=>[P1|[P1]].
by rewrite ger0_real// c2r_ge0. by rewrite -(@ler_r2c _ C) c2rK// r2c0.
Qed.

Lemma etclosed_le (y : C) : closed [set x : C | x <= y].
Proof.
rewrite (_ : mkset _ = (fun x=>-x) @^-1` [set x | -y <= x ]).
apply: closed_comp=>[x _|]; first by apply: opp_continuous.
apply: etclosed_ge.
by rewrite predeqE=>x; rewrite/= lerN2.
Qed.

Lemma etclosed_eq (y : C) : closed [set x : C | x = y].
Proof. exact: closed_eq. Qed.

Lemma etlim_ge_near {T : Type}
  {F : set_system T} {FF : ProperFilter F} (x : C) (u : T -> C) :
    cvg (u @ F) -> (\forall n \near F, x <= u n) -> x <= lim (u @ F).
Proof. by move=> /[swap] /(closed_cvg (>= x))P; apply/P/etclosed_ge. Qed.

Lemma etlimn_ge_near (x : C) (u : C ^nat) : 
  cvgn u -> (\forall n \near \oo, x <= u n) -> x <= limn u.
Proof. exact: etlim_ge_near. Qed.

Lemma etlim_le_near {T : Type}
  {F : set_system T} {FF : ProperFilter F} (x : C) (u : T -> C) :
    cvg (u @ F) -> (\forall n \near F, x >= u n) -> x >= lim (u @ F).
Proof. by move=> /[swap] /(closed_cvg (fun y : C => y <= x))P; apply/P/etclosed_le. Qed.

Lemma etlimn_le_near (x : C) (u : C ^nat) : 
  cvgn u -> (\forall n \near \oo, x >= u n) -> x >= limn u.
Proof. exact: etlim_le_near. Qed.

Lemma ler_etlim_near {T : Type}
  {F : set_system T} {FF : ProperFilter F} (u v : T -> C) : 
    cvg (u @ F) -> cvg (v @ F) ->
      (\forall n \near F, u n <= v n) -> 
        lim (u @ F) <= lim (v @ F).
Proof.
move=> uv cu cv; rewrite -subr_ge0 -limB=>[|//|]; last by apply uv.
apply: etlim_ge_near; first by apply: is_cvgB;[| apply uv].
by apply: filterS cv => n; rewrite subr_ge0.
Qed.

Lemma ler_etlimn_near (u_ v_ : C ^nat) : cvgn u_ -> cvgn v_ ->
  (\forall n \near \oo, u_ n <= v_ n) -> limn u_ <= limn v_.
Proof. exact: ler_etlim_near. Qed.

Lemma etlim_ge {T : Type} {F : set_system T} 
  {FF : ProperFilter F} (x : C) (u : T -> C) : 
    cvg (u @ F) -> (forall n, x <= u n) -> x <= lim (u @ F).
Proof. move=>P1 P2; apply/etlim_ge_near=>//; near=>n; by []. Unshelve. end_near. Qed.

Lemma etlimn_ge (x : C) (u : C ^nat) : cvgn u -> (forall n, x <= u n) -> x <= limn u.
Proof. exact: etlim_ge. Qed.

Lemma etlim_le {T : Type} {F : set_system T} 
  {FF : ProperFilter F} (x : C) (u : T -> C) : 
    cvg (u @ F) -> (forall n, x >= u n) -> x >= lim (u @ F).
Proof. move=>P1 P2; apply/etlim_le_near=>//; near=>n; by []. Unshelve. end_near. Qed.

Lemma etlimn_le (x : C) (u : C ^nat) : cvgn u -> (forall n, u n <= x) -> limn u <= x.
Proof. exact: etlim_le. Qed.

Lemma ler_etlim {T : Type}
  {F : set_system T} {FF : ProperFilter F} (u v : T -> C) :  
  cvg (u @ F) -> cvg (v @ F) ->
    (forall n, u n <= v n) -> 
      lim (u @ F) <= lim (v @ F).
Proof. move=>P1 P2 P3; apply/ler_etlim_near=>//; near=>n; by []. Unshelve. end_near. Qed.

Lemma ler_etlimn (u_ v_ : C^nat) : cvgn u_ -> cvgn v_ ->
  (forall n, u_ n <= v_ n) -> limn u_ <= limn v_.
Proof. exact: ler_etlim. Qed.


(* Lemma etclosed_real : closed [set x : C | x \is Num.real].
Proof.
rewrite (_ : mkset _ = [set x | x <= 0] `|` [set x | 0 <= x ]).
apply: closedU; [apply: etclosed_le|apply: etclosed_ge].
rewrite predeqE=>x; rewrite/= realE; split=>[/orP[]->|[|]->//].
by right. by left. by rewrite orbT.
Qed. *)

Implicit Type (f g: nat -> C) (n: nat) (s a b : C).

(* to use cauchy_seq for other functions *)
Lemma etcvgn_limnP f a :
  f @ \oo --> a <-> forall e, 0 < e -> exists N, forall n,  (N <= n)%N -> `|f n - a| < e.
Proof. exact: cvgn_limnP. Qed.

Lemma etcvgn_subseqP f a : 
  f @ \oo --> a <-> (forall (h: nat -> nat), (forall n, (h n.+1 > h n)%N)
    -> (f \o h) @ \oo --> a).
Proof. exact: cvgn_subseqP. Qed.

Lemma etcvgn_subseqPN f a :
  ~ (f @ \oo --> a) <-> exists e (h: nat -> nat), 
    (forall n, (h n.+1 > h n)%N) /\ 0 < e /\ (forall n, `|(f \o h) n - a| >= e).
Proof. exact: cvgn_subseqPN. Qed.

Definition etcauchy_seq f := forall e, 0 < e -> exists N, forall i j, 
  (N <= i)%N -> (N <= j)%N -> `| f i - f j | < e.

Lemma etcauchy_seqP f : etcauchy_seq f <-> cvgn f.
Proof. exact: cauchy_seqP. Qed.

Definition etcvgn_seq f a := forall e, 0 < e -> exists N : nat, 
    forall i, (N <= i)%N -> `| a - f i | < e.

Lemma etcvgn_seqP f a : etcvgn_seq f a <-> f @ \oo --> a.
Proof. exact: cvgn_seqP. Qed.

(* monotone sequence; can extend to any lattice *)
(* once eventually filter applies to lattice *)
Definition etseq_shift (u_ : C ^nat) := u_ - (fun=>u_ 0%N).
Definition etseq_real (u_ : C ^nat) := forall i, (u_ i) \is Num.real.

Lemma etseq_shiftE (u_ : C ^nat) : etseq_shift u_ = u_ - (fun=>u_ 0%N).
Proof. by []. Qed.
Lemma etseq_shiftEV (u_ : C ^nat) : u_ = etseq_shift u_ + (fun=>u_ 0%N).
Proof. by rewrite etseq_shiftE addrNK. Qed.

Lemma etnondecreasing_shift (u_ : C ^nat) : 
  nondecreasing_seq u_ <-> nondecreasing_seq (etseq_shift u_).
Proof. by split=>H i j /H; rewrite lerD2r. Qed.

Lemma etnondecreasing_shift_real (u_ : C ^nat) : 
  nondecreasing_seq u_ -> etseq_real (etseq_shift u_).
Proof. by move=>H i; rewrite ger0_real// subr_ge0 H. Qed.

Lemma etseq_shift_cvgn (u_ : C ^nat) a:
  (etseq_shift u_ @ \oo --> a) -> u_ @ \oo --> a + u_ 0%N.
Proof.
move=>P1; rewrite [u_]etseq_shiftEV.
by apply: cvgD=>//; rewrite /etseq_shift !fctE addrNK; apply: cvg_cst.
Qed.

Lemma etseq_shift_is_cvgnE (u_ : C ^nat) : cvgn (etseq_shift u_) = cvgn u_.
Proof. by rewrite /etseq_shift; apply/is_cvgDlE; apply: is_cvgN; apply: is_cvg_cst. Qed.

Lemma etseq_shift_limn (u_ : C ^nat) :
  cvgn u_ -> limn u_ = limn (etseq_shift u_) + u_ 0%N.
Proof.
rewrite -etseq_shift_is_cvgnE=>/etseq_shift_cvgn; 
rewrite cvgn_limnE=>[[]//|]; apply/norm_hausdorff.
Qed.

Lemma etlimn_real (u_ : C ^nat) : etseq_real u_ ->
  cvgn u_ -> limn u_ \is Num.real.
Proof. by move=>P; apply: (closed_cvg _ etclosed_real)=>//; exists 0%N=>/=. Qed.

Lemma c2r_cvgn_real (u_ : C ^nat) (x : R) : etseq_real u_ ->
  ((c2r \o u_) @ \oo --> x) -> (u_ @ \oo --> r2c x).
Proof.
move=>ru cu; have ->: u_ = r2c \o (c2r \o u_) 
  by apply/funext=>i; rewrite !fctE c2rK//.
apply: etcvg_mapV=>//; apply r2c_continuous.
Qed.

Lemma c2r_cvgn_realV (u_ : C ^nat) a : 
  u_ @ \oo --> a -> (c2r \o u_) @ \oo --> c2r a.
Proof. by move=>cu; apply: etcvg_map=>//; apply: c2r_continuous. Qed.

Lemma etnondecreasing_cvgn (u_ : C ^nat) (M : C) :
      nondecreasing_seq u_ -> (forall n : nat, u_ n <= M) -> 
        u_ @ \oo --> r2c (limn (c2r \o (etseq_shift u_))) + u_ 0%N.
Proof.
move=>nd ub; move: {+}nd {+}nd=>/etnondecreasing_shift P1/etnondecreasing_shift_real P2.
pose v i := c2r ((etseq_shift u_) i).
have cv: cvgn v. apply: nondecreasing_is_cvgn.
  by move=>n m Pnm; rewrite /v -(@ler_r2c _ C) !c2rK// P1.
  exists (c2r (M - u_ 0%N))=>i [x] _ <-.
  rewrite -(@ler_r2c _ C) /v !c2rK//.
  by rewrite lerD2r. by rewrite ger0_real// subr_ge0.
have Pu: u_ = (r2c \o v) + (fun=>u_ 0%N)
by apply/funext=>i; rewrite !fctE /v c2rK// addrNK.
rewrite {1}Pu; apply: cvgD; last by apply: cvg_cst.
apply: etcvg_mapV. apply: r2c_continuous. apply: cv.
Qed.

Lemma etnondecreasing_is_cvgn (u_ : C ^nat) (M : C) :
       nondecreasing_seq u_ -> (forall n : nat, u_ n <= M) -> cvgn u_.
Proof.
move=>nd ub. apply/cvg_ex; exists (r2c (limn (c2r \o (etseq_shift u_))) + u_ 0%N).
apply: (etnondecreasing_cvgn nd ub).
Qed.

Lemma etnonincreasing_cvgn (u_ : C ^nat) (M : C) :
      nonincreasing_seq u_ -> (forall n : nat, M <= u_ n) -> 
       u_ @ \oo --> r2c (limn (c2r \o (etseq_shift u_))) + u_ 0%N.
Proof.
rewrite -nondecreasing_opp=>P1 P2.
have P3 n: (-u_) n <= (-M) by rewrite fctE lerN2.
move: (etnondecreasing_cvgn P1 P3)=>/cvgN.
rewrite opprK opprD -rmorphN -limN.
rewrite [in (-u_) 0%N]fctE opprK.
suff ->: (- (c2r \o etseq_shift (- u_))) = (c2r \o etseq_shift u_) by [].
by apply/funext=>i; rewrite/etseq_shift !fctE -c2rN opprB opprK addrC.
apply: is_etcvg_map. apply: c2r_continuous.
by rewrite etseq_shift_is_cvgnE; apply: etnondecreasing_is_cvgn.
Qed.

Lemma etnonincreasing_is_cvgn (u_ : C ^nat) (M : C) :
       nonincreasing_seq u_ -> (forall n : nat, M <= u_ n) -> cvgn u_.
Proof.
rewrite -nondecreasing_opp -is_cvgNE =>P1 P2.
apply: (@etnondecreasing_is_cvgn _ (- M) P1 _)=>n.
by rewrite {1}/GRing.opp/= Num.Theory.lerN2.
Qed.

Lemma etnondecreasing_cvgn_le (u_ : C ^nat) :
       nondecreasing_seq u_ -> cvgn u_ -> (forall n : nat, u_ n <= limn u_).
Proof.
move=>nd cu n. move: {+}nd=>/etnondecreasing_shift_real rus.
move: {+}cu; rewrite -etseq_shift_is_cvgnE=>cus.
rewrite etseq_shift_limn// -lerBlDr.
suff: (c2r \o (etseq_shift u_)) n <= limn (c2r \o (etseq_shift u_)).
rewrite etlim_map//; last by apply: c2r_continuous.
rewrite/= -[c2r _ <= _]subr_ge0 -c2rB -(@r2c_ge0 _ C) c2rK.
by rewrite subr_ge0 /etseq_shift !fctE.
apply: realB=>//. apply: etlimn_real=>//.
apply: nondecreasing_cvgn_le=>[i j leij/=|].
by rewrite ler_c2r//; move: nd=>/etnondecreasing_shift/(_ _ _ leij).
apply: is_etcvg_map=>//; apply: c2r_continuous.
Qed.

Lemma etnonincreasing_cvgn_ge (u_ : C ^nat) : 
  nonincreasing_seq u_ -> cvgn u_ -> (forall n, limn u_ <= u_ n).
Proof.
rewrite -nondecreasing_opp -is_cvgNE =>P1 P2 n.
rewrite -(opprK u_) limN// lerN2.
by apply etnondecreasing_cvgn_le.
Qed.

Lemma lt_etlimn (u : C ^nat) (x : C) : nondecreasing_seq u -> 
  cvgn u -> x < limn u -> \forall n \near \oo, x <= u n.
Proof.
move=> ndu cu Ml; have [[n Mun]|/forallNP Mu] := pselect (exists n, x <= u n).
  near=> m; suff : u n <= u m by exact: le_trans.
  by near: m; exists n.+1 => // p q; apply/ndu/ltnW.
have Cn n : comparable x (u n) by apply/(comparabler_trans 
  (lt_comparable Ml))/ge_comparable/etnondecreasing_cvgn_le.
have {}Mu : forall y, x > u y. move=> y. rewrite comparable_ltNge. by apply/negP.
by rewrite comparable_sym.
have : limn u <= x by apply etlimn_le_near => //; near=> m; apply/ltW/Mu.
by move/(lt_le_trans Ml); rewrite ltxx.
Unshelve. all: by end_near.
Qed.

Lemma gt_etlimn (u : C ^nat) (x : C) : nonincreasing_seq u -> 
  cvgn u -> x > limn u -> \forall n \near \oo, x >= u n.
Proof.
rewrite -nondecreasing_opp=>P1 P2.
rewrite -ltrN2 -limN// =>P3.
near=>n. suff: -x <= (-u) n by rewrite fctE lerN2. near: n.
by rewrite near_simpl; apply: lt_etlimn=>//; apply: is_cvgN.
Unshelve. end_near.
Qed.

End ExtNumMono.

Definition etsup {R : realType} {C : extNumType R} := @supremum _ C 0.
Definition etinf {R : realType} {C : extNumType R} (E : set C) := - etsup (-%R @` E).

Section SetComparable.
Variable (C : numFieldType).
Implicit Type (E : set C).

Definition set_comparable E := forall x y, E x -> E y -> x >=< y.

Lemma comparable_get E : set_comparable E -> 
  forall x, E x -> x >=< get E.
Proof. by move=>Pc x Ex; move: (getI Ex); apply: Pc. Qed.

Lemma comparable_get_ubound E x : E !=set0 ->
  ubound E x -> x >=< get E.
Proof. move=>[y Py] P. apply ge_comparable. apply P. apply (getI Py). Qed.

Lemma comparablerN (R : numDomainType) (x y : R) :
  (-x >=< -y) = (x >=< y).
Proof. by rewrite !comparablerE opprK addrC -realN opprB. Qed.

Lemma comparablerDl (R : numDomainType) (z x y : R) :
  (x + z >=< y + z) = (x >=< y).
Proof. by rewrite !comparablerE [y+z]addrC addrKA. Qed.

Lemma comparablerDr (R : numDomainType) (z x y : R) :
  (z + x >=< z + y) = (x >=< y).
Proof. by rewrite !comparablerE [z+x]addrC addrKA. Qed.

Lemma set_comparableNE E : set_comparable [set - x | x in E] <-> set_comparable E.
Proof.
split=>[P x y/=Ex Ey|P x y/=[a Ea <-][b Eb <-]]. 
by rewrite -comparablerN; apply: P=>/=; [exists x|exists y].
by rewrite comparablerN; apply: P.
Qed.

Lemma contra_ler_forall (x : C) : ~ (forall x1, x <= x1).
Proof.
move=>P. have P1: (x = 0). 
apply/le_anti/andP; split; last rewrite -(lerD2l x) -lerBrDr; by apply P.
rewrite P1 in P. move: (P (-1)).
by rewrite -lerN2 opprK oppr0 ler10 .
Qed.

Lemma ubound_supremumE E x0 x : ubound E x -> 
  (forall y, ubound E y -> x <= y) -> supremum x0 E = x.
Proof.
move=>P2 P3; rewrite /supremum; case: eqP=>P4.
apply/le_anti/andP; split; first rewrite -(lerD2l x) -lerBrDr;
by apply P3; rewrite P4/ubound/=.
apply xget_subset1=>//; by apply is_subset1_supremums.
Qed.

(* Lemma foo8 E x0 : supremums E !=set0 -> 
  ubound E (supremum x0 E) /\ lbound (ubound E) (supremum x0 E).
Proof.
case=> x Ax; rewrite /supremum; move: Ax; case: ifPn => [/eqP -> //|_].
by rewrite/supremums/=/ubound/lbound/==>[[_ P1]]; exfalso; apply (@contra_ler_forall x)=>x1; apply P1.
by move=>Ax; split; case: xgetP => [y yA [P1 P2]|/(_ x) //].
Qed. *)

End SetComparable.


Section extnumsup.
Context {R : realType} {C : extNumType R}.
Implicit Type (E : set C) (F : set R).

Lemma c2rKB (x y : C) : x >=< y -> r2c (c2r (x - y)) = x - y.
Proof. by rewrite comparablerE=>P; rewrite c2rK. Qed.

Lemma nonempty_imageE (S T: Type) (f : S -> T) (F : set S) :
  (f @` F !=set0) = (F !=set0).
Proof. by rewrite propeqE; split=>[|[x Px]]; [apply: nonempty_image|exists (f x)]. Qed.

Lemma image_set0E (S T: Type) (f : S -> T) (F : set S) :
  (f @` F == set0) = (F == set0).
Proof.
case: eqP. by move=>/image_set0_set0->; rewrite eqxx.
by case: eqP=>// ->; rewrite image_set0.
Qed.

Definition c2r_shift E := c2r @` ((fun x=> x - get E) @` E).
Definition r2c_shift (x0 : C) (F : set R) : set C := (fun x=>x + x0) @` (r2c @` F).

Lemma c2r_shiftK E : set_comparable E ->
  r2c_shift (get E) (c2r_shift E) = E.
Proof.
move=>Pc; rewrite predeqE=>x; split;
rewrite /c2r_shift/r2c_shift/=.
move=>[a][b][c][d] Ed<-<-<-.
by rewrite c2rKB ?addrNK// => [ <-//|]; apply comparable_get.
move=>Ex. exists (x - get E); rewrite ?addrNK//.
exists (c2r (x - get E)); last by rewrite c2rKB//; apply/comparable_get.
by exists (x - get E)=>//; exists x.
Qed.

Lemma c2r_shiftP E (x : C) : set_comparable E -> 
  E x -> c2r_shift E (c2r (x - get E)).
Proof. by move=>P1 P2; rewrite/c2r_shift/=; exists (x-get E)=>//; exists x. Qed.

Lemma has_ubound_comparable E : has_ubound E -> set_comparable E.
Proof.
move=>[u Pu] x y Ex Ey; move: (Pu x Ex) (Pu y Ey)=>/le_comparable +/le_comparable.
rewrite [y>=<u]comparable_sym; exact: comparabler_trans.
Qed.

Lemma has_lbound_comparable E : has_lbound E -> set_comparable E.
Proof.
move=>[u Pu] x y Ex Ey; move: (Pu x Ex) (Pu y Ey)=>/le_comparable +/le_comparable.
rewrite comparable_sym; exact: comparabler_trans.
Qed.

Lemma has_sup_comparable E : has_sup E -> set_comparable E.
Proof. move=>[]Ps; apply/has_ubound_comparable. Qed.

Lemma has_inf_comparable E : has_inf E -> set_comparable E.
Proof. move=>[]Ps; apply/has_lbound_comparable. Qed.

Lemma r2c_shift_comparable (x0 : C) (F : set R) : 
  set_comparable (r2c_shift x0 F).
Proof.
move=>x y[]a/=[ar]Far<-<-[]b/=[br]Fbr<-<-; 
by rewrite-subr_comparable0 [r2c br + _]addrC addrKA comparablerE subr0 -raddfB r2c_real.
Qed.

Lemma c2r_shift_ubound E : set_comparable E -> 
  forall x, ubound (c2r_shift E) x = ubound E (r2c x + get E).
Proof.
move=>Pc x; rewrite propeqE; split.
move=>Pu y Ey. rewrite -lerBlDr -c2rKB 1?ler_r2c/=.
by apply/Pu/c2r_shiftP. by apply/comparable_get.
move=>Pu y Ey. rewrite -(@ler_r2c _ C) -(lerD2r (get E)).
apply: Pu. move: Ey; rewrite/c2r_shift/==>[[a][b Eb]]<-<-.
by rewrite c2rKB ?addrNK//; apply/comparable_get.
Qed.

Lemma c2r_ubound E : set_comparable E -> E !=set0 ->
  ubound E = r2c_shift (get E) (ubound (c2r_shift E)).
Proof.
move=>Pc [x0 Px0]; rewrite predeqE=>x; split.
move=>ux; rewrite/r2c_shift/=; exists (x - get E); rewrite?addrNK//.
exists (c2r (x - get E)). rewrite c2r_shift_ubound//.
1,2: rewrite c2rKB// ?addrNK//; move: (ux _ Px0)=>/le_comparable;
by rewrite comparable_sym=>P; apply: (comparabler_trans P); apply: comparable_get.
by rewrite/r2c_shift/==>[[a][b Pb]<-<-]; rewrite -c2r_shift_ubound.
Qed.

Lemma has_sup_c2r_shift (E : set C) : has_sup E -> has_sup (c2r_shift E).
Proof. 
move=>[P1 [x P2]]; split; first by rewrite !nonempty_imageE.
exists (c2r (x - (get E)))=>y [a/= [b Pb]]<-<-.
by apply/ler_c2r/lerB=>//; apply P2.
Qed.

Lemma sup_least_ubound (F : set R) : has_sup F -> lbound (ubound F) (sup F).
Proof.
move=>P1. rewrite/lbound/==>x P2.
case: leP=>//. rewrite -subr_gt0=>/sup_adherent/(_ P1)[e P3].
rewrite subKr. move: P2. rewrite /ubound/==>/(_ _ P3).
by case: leP.
Qed.

Lemma etsup_shift E : has_sup E ->
  etsup E = r2c (sup (c2r_shift E)) + get E.
Proof.
move=>P1. move: (has_sup_c2r_shift P1) (has_sup_comparable P1)=>P2 P5.
move: (sup_least_ubound P2) (sup_upper_bound P2)=>P3 P4.
set F := c2r_shift E in P2 P3 P4 *.
rewrite /etsup. apply/ubound_supremumE.
rewrite /ubound/==>x Px. rewrite -lerBlDr -c2rKB 1?ler_r2c.
by apply/P4/c2r_shiftP. by apply/comparable_get.
move=>y P6. rewrite -lerBrDr -c2rKB.
rewrite ler_r2c. apply P3. rewrite c2r_shift_ubound// c2rKB ?addrNK//.
all: by apply comparable_get_ubound=>//; move: P1=>[].
Qed.

Lemma etsup_adherent (E : set C) (eps : C) : 0 < eps ->
  has_sup E -> exists2 e : C, E e & (etsup E - eps) < e.
Proof.
move=>P1 P2. have P3: 0 < c2r eps by apply/c2r_gt0.
move: (sup_adherent P3 (has_sup_c2r_shift P2))=>[er P4 P5].
exists (r2c er + get E).
move: P4. rewrite /c2r_shift/==>[[e1 [e2]]]P6 <-<-.
by rewrite c2rK ?addrNK// -comparablerE comparable_get//; apply has_sup_comparable.
rewrite etsup_shift// addrC addrA ltrD2 addrC -[eps]c2rK.
by rewrite -rmorphB ltr_r2c. by apply gtr0_real.
Qed.

Lemma etsup_upper_bound E : has_sup E -> ubound E (etsup E).
Proof.
move=>P1. rewrite etsup_shift// -c2r_shift_ubound.
by apply/sup_upper_bound/has_sup_c2r_shift. by apply/has_sup_comparable.
Qed.

Lemma etsup_least_ubound E : has_sup E -> lbound (ubound E) (etsup E).
Proof.
move=>P1. rewrite/lbound/==>x P2.
rewrite etsup_shift// -lerBrDr -c2rKB 1?ler_r2c.
apply/sup_least_ubound. by apply/has_sup_c2r_shift. rewrite c2r_shift_ubound ?c2rKB ?addrNK//.
1,3: by apply/comparable_get_ubound=>//; move: P1=>[].
by apply/has_sup_comparable.
Qed.

End extnumsup.

Section MxExtNumCvg.
Variable (R: realType) (C: extNumType R) (m n : nat).
Local Notation M := 'M[C]_(m,n).
Implicit Type (f g: nat -> M) (r: nat) (a b : M) (s : nat -> C) (k: C).

Lemma mxhausdorff p q : hausdorff_space 'M[C]_(p,q).
Proof.
case: p=>[|p]; last first. case: q=>[|q]; last by apply: norm_hausdorff.
all: rewrite ball_hausdorff=>/=a b /negP Pab; exfalso; apply Pab; apply/eqP;
apply/matrixP=>i j. by destruct j. by destruct i.
Qed.

Lemma mxcvgn_limnE f a : f @ \oo --> a <-> limn f = a /\ cvgn f.
Proof. 
split=>[P1|[ <-]//]. split. apply/cvg_lim. apply mxhausdorff.
apply P1. by move: P1=>/cvgP.
Qed.

(* for quick use. directly use these lemmas have the problem on different canonical routes *)

Lemma mxcvgn_cst a : (fun n:nat=>a) @ \oo --> a. Proof. exact: cvg_cst. Qed.
Lemma is_mxcvgn_cst a : cvgn (fun n:nat=>a). Proof. exact: is_cvg_cst. Qed.
Lemma mxlimn_cst a : limn (fun n:nat=>a) = a. Proof. apply: lim_cst. apply mxhausdorff. Qed.

Lemma mxcvgnN f a : f @ \oo --> a -> (- f) @ \oo --> - a.
Proof.
case: m f a=>[f a _|m' f a]; [apply mxcvgn_dim0n|].
case: n f a=>[f a _|n' f a]; [apply mxcvgn_dimn0|exact: cvgN].
Qed.

Lemma is_mxcvgnN f : cvgn f -> cvgn (- f).
Proof. by move=> /mxcvgnN /cvgP. Qed.

Lemma is_mxcvgnNE f : cvgn (- f) = cvgn f.
Proof. by rewrite propeqE; split=> /mxcvgnN; rewrite ?opprK => /cvgP. Qed.

Lemma mxcvgnMn f r a : f @ \oo --> a -> ((@GRing.natmul _)^~r \o f) @ \oo --> a *+ r.
Proof.
case: m f a=>[f a _|m' f a]; [apply mxcvgn_dim0n|].
case: n f a=>[f a _|n' f a]; [apply mxcvgn_dimn0|exact: cvgMn].
Qed.

Lemma is_mxcvgnMn f r : cvgn f -> cvgn ((@GRing.natmul _)^~r \o f).
Proof. by move=> /(@mxcvgnMn _ r) /cvgP. Qed.

Lemma mxcvgnD f g a b : f @ \oo --> a -> g @ \oo --> b -> (f + g) @ \oo --> a + b.
Proof.
case: m f g a b=>[f g a b _ _|m' f g a b]; [apply mxcvgn_dim0n|].
case: n f g a b=>[f g a b _ _|n' f g a b]; [apply mxcvgn_dimn0|exact: cvgD].
Qed.

Lemma is_mxcvgnD f g : cvgn f -> cvgn g -> cvgn (f + g).
Proof. by have := cvgP _ (mxcvgnD _ _); apply. Qed.

Lemma mxcvgnB f g a b : f @ \oo --> a -> g @ \oo --> b -> (f - g) @ \oo --> a - b.
Proof. by move=> ? ?; apply: mxcvgnD=>[//|]; apply: mxcvgnN. Qed.

Lemma is_mxcvgnB f g : cvgn f -> cvgn g -> cvgn (f - g).
Proof. by have := cvgP _ (mxcvgnB _ _); apply. Qed.

Lemma is_mxcvgnDlE f g : cvgn g -> cvgn (f + g) = cvgn f.
Proof.
move=> g_cvg; rewrite propeqE; split; last by move=> /is_mxcvgnD; apply.
by move=> /is_mxcvgnB /(_ g_cvg); rewrite addrK.
Qed.

Lemma is_mxcvgnDrE f g : cvgn f -> cvgn (f + g) = cvgn g.
Proof. by rewrite addrC; apply: is_mxcvgnDlE. Qed.

Lemma mxcvgnZ s f k a : s @ \oo --> k -> f @ \oo --> a
  -> (fun x => s x *: f x) @ \oo --> k *: a.
Proof.
case: m f a=>[f a _ _|m' f a]; [apply mxcvgn_dim0n|].
case: n f a=>[f a _ _|n' f a]; [apply mxcvgn_dimn0|exact: cvgZ].
Qed.

Lemma is_mxcvgnZ s f : cvgn s -> cvgn f -> cvgn (fun x => s x *: f x).
Proof. by have := cvgP _ (mxcvgnZ _ _); apply. Qed.

Lemma mxcvgnZl s k a : s @ \oo --> k -> (fun x => s x *: a) @ \oo --> k *: a.
Proof. by move=> ?; apply: mxcvgnZ => //; exact: cvg_cst. Qed.

Lemma is_mxcvgnZl s a : cvgn s -> cvgn (fun x => s x *: a).
Proof. by have := cvgP _ (mxcvgnZl  _); apply. Qed.

Lemma mxcvgnZr k f a : f @ \oo --> a -> k \*: f @ \oo --> k *: a.
Proof. apply: mxcvgnZ => //; exact: cvg_cst. Qed.

Lemma is_mxcvgnZr k f : cvgn f -> cvgn (k *: f ).
Proof. by have := cvgP _ (mxcvgnZr  _); apply. Qed.

Lemma is_mxcvgnZrE k f : k != 0 -> cvgn (k *: f) = cvgn f.
Proof.
move=> k_neq0; rewrite propeqE; split => [/(@mxcvgnZr k^-1)|/(@mxcvgnZr k)/cvgP//].
by under [_ \*: _]funext => x /= do rewrite scalerK//; apply: cvgP.
Qed.

Lemma mxlimnN f : cvgn f -> limn (- f) = - limn f.
Proof. by move=> ?; apply: cvg_lim; [apply mxhausdorff|apply: mxcvgnN]. Qed.

Lemma mxlimnD f g : cvgn f -> cvgn g -> limn (f + g) = limn f + limn g.
Proof. move=> Pf Pg; apply: cvg_lim; [apply mxhausdorff|apply: mxcvgnD;[apply Pf|apply Pg]]. Qed.

Lemma mxlimnB f g : cvgn f -> cvgn g -> limn (f - g) = limn f - limn g.
Proof. move=> Pf Pg; apply: cvg_lim; [apply mxhausdorff|apply: mxcvgnB;[apply Pf|apply Pg]]. Qed.

Lemma mxlimnZ s f : cvgn s -> cvgn f -> limn (fun x => s x *: f x) = limn s *: limn f.
Proof. move=> Ps Pf; apply: cvg_lim; [apply mxhausdorff|apply: mxcvgnZ;[apply Ps|apply Pf]]. Qed.

Lemma mxlimnZl s a : cvgn s -> limn (fun x => s x *: a) = limn s *: a.
Proof. by move=> ?; apply: cvg_lim; [apply mxhausdorff|apply: mxcvgnZl]. Qed.

Lemma mxlimnZr k f : cvgn f -> limn (k *: f) = k *: limn f.
Proof. by move=> ?; apply: cvg_lim; [apply mxhausdorff|apply: mxcvgnZr]. Qed.

(* since only nontrivial matrix are canonical to normZmodType *)
Lemma mxcvgn_norm (h : nat->'M[C]_(m.+1,n.+1)) (x : 'M[C]_(m.+1,n.+1)) : 
  h @ \oo --> x -> (Num.norm \o h) @ \oo --> `|x|.
Proof. exact: cvg_norm. Qed.
Lemma is_mxcvgn_norm (h : nat->'M[C]_(m.+1,n.+1)) : 
  cvgn h -> cvgn (Num.norm \o h).
Proof. exact: is_cvg_norm. Qed.
Lemma mxlimn_norm (h : nat->'M[C]_(m.+1,n.+1)) : 
  cvgn h -> limn (Num.norm \o h) = `|limn h|.
Proof. exact: lim_norm. Qed.

Lemma mxcvgn_map f a (V : completeType) (h : M -> V) :
  continuous h -> f @ \oo --> a -> (h \o f) @ \oo --> h a.
Proof. 
move=>ch cvgf; apply: (@cvg_fmap _ _ (nbhs (f @ \oo)) a h).
by apply ch. by apply cvgf.
Qed.

Lemma mxcvgn_mapV (V : completeType) (h : V -> M) (h' : nat -> V) (a : V) :
  continuous h -> h' @ \oo --> a -> (h \o h') @ \oo --> h a.
Proof. 
move=>ch cvgf; apply: (@cvg_fmap _ _ (nbhs (h' @ \oo)) a h).
by apply ch. by apply cvgf.
Qed.

Lemma is_mxcvgn_map f (V : completeType) (h : M -> V) :
  continuous h -> cvgn f -> cvgn (h \o f).
Proof.
move=>P1 /cvg_ex=>[/= [a Pa]]. apply/cvg_ex.
exists (h a). by move: (mxcvgn_map P1 Pa).
Qed.

Lemma is_mxcvgn_mapV (V : completeType) (h : V -> M) (h' : nat -> V) :
  continuous h -> cvgn h' -> cvgn (h \o h').
Proof.
move=>P1 /cvg_ex=>[/= [a Pa]]. apply/cvg_ex.
exists (h a). by move: (mxcvgn_mapV P1 Pa).
Qed.

Lemma mxlimn_map f a (V : completeType) (h : M -> V) :
  hausdorff_space V -> continuous h -> cvgn f -> limn (h \o f) = h (limn f).
Proof. by move=>hV ch; move/(mxcvgn_map ch)/cvg_lim=>/(_ hV). Qed.

Lemma mxlimn_mapV (V : completeType) (h : V -> M) (h' : nat -> V) :
  continuous h -> cvgn h' -> limn (h \o h') = h (limn h').
Proof. by move=>ch; move/(mxcvgn_mapV ch)/cvg_lim=>/(_ (@mxhausdorff _ _)). Qed.

Lemma is_mxcvgnZlE s a : a != 0 -> cvgn (fun x => s x *: a) = cvgn s.
Proof.
move=> a_neq0; rewrite propeqE; split; last by apply is_mxcvgnZl.
have [i [j Pij]] : exists i j, a i j != 0.
move: a_neq0. apply contraPP. rewrite -forallNP=>P.
apply/negP. rewrite negbK. apply/eqP/matrixP=>i j.
move: (P i). rewrite -forallNP=>/(_ j)/negP. by rewrite mxE negbK=>/eqP->.
set t := (fun x : M => (x i j) / (a i j)).
have P1: s = t \o (fun x : nat => s x *: a).
rewrite funeqE=>p. rewrite /= /t mxE mulfK//.
move=>P. rewrite P1. apply/is_mxcvgn_map=>//.
move=>/= x w/= /nbhs_ballP [/=e egt0 Pb].
apply/nbhs_ballP. have P2: 0 < `|a i j|.
rewrite lt_def normr_ge0 andbT.
by move: Pij; apply contraNN=>/eqP/Num.Theory.normr0P.
exists (e * `|a i j|) =>//=. apply Num.Theory.mulr_gt0=>//.
move=> y /= Pxy. apply (Pb (t y)). move: Pxy.
rewrite /ball/= /mx_ball=>/(_ i j). rewrite /ball/=.
rewrite /t -mulrBl Num.Theory.normrM Num.Theory.normrV ?GRing.unitfE//.
rewrite Num.Theory.ltr_pdivrMr// =>P3.
Qed.

(* Lemma mxcvgn_limnP (p q:nat) (f: nat -> 'M_(p.+1, q.+1)) (a: 'M_(p.+1, q.+1)) :
f @ \oo --> a <-> forall e, 0 < e -> exists N, forall n,  (N <= n)%N -> `|f n - a| < e.
Proof. move: f a. apply (@cvgn_limnP R 'M_(p.+1, q.+1)).
exact: cvgn_limnP. *)

Lemma mxcvgn_limnP p q (h: nat -> 'M[C]_(p,q)) (x : 'M[C]_(p,q)) :
  h @ \oo --> x <-> forall e, 0 < e -> exists N, forall n,  (N <= n)%N -> mx_norm (h n - x) < e.
Proof.
case: p h x=>[h x|p]; last case: q=>[h x|q h x].
1,2: split=>_; [move=>e Pe; exists 0%N=>r _; rewrite !mx_dim0 mx_norm0//|].
apply mxcvgn_dim0n. apply mxcvgn_dimn0. rewrite mx_normEV.
exact: cvgn_limnP.
Qed.

Lemma mxcvgn_subseqP p q (h: nat -> 'M[C]_(p,q)) (x : 'M[C]_(p,q)) : 
  h @ \oo --> x <-> (forall (h': nat -> nat), (forall n, (h' n.+1 > h' n)%N) -> (h \o h') @ \oo --> x).
Proof.
case: p h x=>[h x|p]; last case: q=>[h x|q h x].
1,2: split=>_; [move=>??|]; rewrite !mx_dim0; apply: cvg_cst.
exact: cvgn_subseqP.
Qed.

Lemma mxcvgn_subseqPN p q (h: nat -> 'M[C]_(p,q)) (x : 'M[C]_(p,q)) :
  ~ (h @ \oo --> x) <-> exists e (h': nat -> nat), 
    (forall n, (h' n.+1 > h' n)%N) /\ 0 < e /\ (forall n, mx_norm ((h \o h') n - x) >= e).
Proof.
case: p h x=>[h x|p]; last case: q=>[h x|q h x].
1,2: rewrite not_existsP; rewrite iff_not2; split=>_;[|rewrite !mx_dim0; apply: cvg_cst].
1,2: move=>c; rewrite -forallNP=> h'; rewrite !not_andP; right.
1,2: case E: (0 < c); [right|left=>//]; rewrite -existsNP; exists 0%N; rewrite !mx_dim0 mx_norm0.
1,2: by apply/negP; rewrite -Num.Theory.real_ltNge// ?Num.Theory.real0// Num.Theory.gtr0_real.
rewrite mx_normEV.
exact: cvgn_subseqPN.
Qed.

Lemma mxnatmul_continuous p : continuous (fun x : M => x *+ p).
Proof.
case: m=>/=[x|m']; last case: n=>/=[x|n' x].
1,2: rewrite !mx_dim0; apply: cst_continuous.
exact: natmul_continuous.
Qed.

Lemma mxscale_continuous : continuous (fun z : C * M => z.1 *: z.2).
Proof.
case: m=>/=[x|m']; last case: n=>/=[x|n' x].
1,2: rewrite !mx_dim0; apply: cst_continuous.
exact: scale_continuous.
Qed.

Global Arguments mxscale_continuous _ _ : clear implicits.

Lemma mxscaler_continuous k : continuous (fun x : M => k *: x).
Proof.
by move=> x; apply: (cvg_comp2 (cvg_cst _) cvg_id (mxscale_continuous (_, _))).
Qed.

Lemma mxscalel_continuous (x : M) : continuous (fun k : C => k *: x).
Proof.
by move=> k; apply: (cvg_comp2 cvg_id (cvg_cst _) (mxscale_continuous (_, _))).
Qed.

(* TODO: generalize to pseudometricnormedzmod *)
Lemma mxopp_continuous : continuous (fun x : M => -x).
Proof.
case: m=>/=[x|m']; last case: n=>/=[x|n' x].
1,2: rewrite !mx_dim0; apply: cst_continuous.
exact: opp_continuous.
Qed.

Lemma mxadd_continuous : continuous (fun z : M * M => z.1 + z.2).
Proof.
case: m=>/=[x|m']; last case: n=>/=[x|n' x].
1,2: rewrite !mx_dim0; apply: cst_continuous.
exact: add_continuous.
Qed.

Global Arguments mxadd_continuous _ _ : clear implicits.

Lemma mxaddr_continuous a : continuous (fun z : M => a + z).
Proof.
by move=> x; apply: (cvg_comp2 (cvg_cst _) cvg_id (mxadd_continuous (_, _))).
Qed.

Lemma mxaddl_continuous a : continuous (fun z : M => z + a).
Proof.
by move=> x; apply: (cvg_comp2 cvg_id (cvg_cst _) (mxadd_continuous (_, _))).
Qed.

(* Variable (f : nat -> 'M[R[i]]_(m,n)) (a : 'M[R[i]]_(m,n)). *)
Definition mxcauchy_seq f := 
  forall e, 0 < e -> exists N, forall i j, 
  (N <= i)%N -> (N <= j)%N -> mx_norm (f i - f j) < e.

Definition mxcvgn_seq f a := 
  forall e, 0 < e -> exists N : nat, 
    forall i, (N <= i)%N -> mx_norm (a - f i) < e.

Lemma mxcauchy_seqP f : mxcauchy_seq f <-> cvgn f.
Proof.
rewrite /mxcauchy_seq; case: m f=>[f|]; last case: n=>[m' f|m' n' f].
1,2: split=>_. apply/is_mxcvgn_dim0n. 2: apply/is_mxcvgn_dimn0.
1,2: by move=>e egt0; exists 0%N=>i j _ _; rewrite !mx_dim0 mx_norm0.
exact: (@cauchy_seqP _ 'M[C]_(n'.+1,m'.+1)).
Qed.

Lemma mxcvgn_seqP f a : mxcvgn_seq f a <-> f @ \oo --> a.
Proof.
rewrite /mxcvgn_seq; case: m f a=>[f a|]; last case: n=>[m' f a|m' n' f a].
1,2: split=>[_ |_ e egt0]; last exists 0%N=>i _. 
1,2,3,4: rewrite !mx_dim0 ?mx_norm0//. apply/mxcvgn_dim0n. apply/mxcvgn_dimn0.
exact: (@cvgn_seqP _ 'M[C]_(n'.+1,m'.+1)).
Qed.

End MxExtNumCvg.

Section MxLinearContinuous.
Variable (R: realType) (C: extNumType R).

Lemma mxlinear_continuous m n p q (f : 'M[C]_(m,n) -> 'M[C]_(p,q)) :
  linear f -> continuous f.
Proof.
move: f; case: m=>[|m]; last first. case: n=>[|n]; last first. 
case: p=>[|p]; last first. case: q=>[|q]; last first.
all: move=>f Lf; set LfT : GRing.Linear.type _ _ :=
  HB.pack f (GRing.isLinear.Build _ _ _ _ f Lf);
have P0 : f = LfT by [].
suff: continuous LfT by [].
rewrite -linear_bounded_continuous -bounded_funP=>r/=.
have Pu : exists c, forall i j, `|LfT (delta_mx i j)| <= c.
exists (\sum_i\sum_j`|LfT (delta_mx i j)|)=>i j.
rewrite (bigD1 i)//= (bigD1 j)//= -addrA Num.Theory.lerDl Num.Theory.addr_ge0//.
1,2: rewrite Num.Theory.sumr_ge0//. move=>k _; rewrite Num.Theory.sumr_ge0//.
move: Pu=>[c Pc]. exists ((m.+1)%:R * ((n.+1)%:R * (r * c)))=>x /mxnorm_le_alter Pij.
(* have Pij i j : `|x i j| <= r. by apply (le_trans (mx_norm_element _ (i,j))). *)
rewrite (matrix_sum_delta x) P0 linear_sum/=.
apply: (le_trans (ler_norm_sum _ _ _)). apply/ler_sum_const=>i.
rewrite P0 linear_sum/=.
apply: (le_trans (ler_norm_sum _ _ _)). apply/ler_sum_const=>j.
by rewrite P0 linearZ/= normrZ ler_pM//; move: (Pij (i,j)).
all: by apply: cst_continuous_eq; exists 0; apply/funext=>i; 
  rewrite !mx_dim0// P0 linear0.
Qed.

Lemma mxcvgn_lfun m n p q (f : 'M[C]_(m,n) -> 'M[C]_(p,q))
  (u : nat -> 'M[C]_(m,n)) (a : 'M[C]_(m,n)) : 
  linear f -> u @ \oo --> a -> (fun x=> f (u x)) @ \oo --> (f a).
Proof. by move/mxlinear_continuous=>P1; apply: continuous_cvg; apply: P1. Qed.

Lemma is_mxcvgn_lfun m n p q (f : 'M[C]_(m,n) -> 'M[C]_(p,q))
(u : nat -> 'M[C]_(m,n))  : linear f -> cvgn u -> cvgn (f \o u).
Proof. by move=>P1; have := cvgP _ (mxcvgn_lfun P1 _); apply. Qed.

Lemma mxlimn_lfun m n p q (f : 'M[C]_(m,n) -> 'M[C]_(p,q))
  (u : nat -> 'M[C]_(m,n)) : 
  linear f -> cvgn u -> limn (f \o u) = f (limn u).
Proof. move=>P1 ?; apply: cvg_lim => //. apply mxhausdorff. by apply: mxcvgn_lfun. Qed.

Lemma mxclosed_comp m n p q (f : 'M[C]_(m,n) -> 'M[C]_(p,q))
  (A : set 'M[C]_(p,q)) :
  linear f -> closed A -> closed (f @^-1` A).
Proof. by move=>lf; apply closed_comp=>x _; apply (mxlinear_continuous lf). Qed.

Lemma mxopen_comp m n p q (f : 'M[C]_(m,n) -> 'M[C]_(p,q))
  (A : set 'M[C]_(p,q)) :
  linear f -> open A -> open (f @^-1` A).
Proof. by move=>lf; apply open_comp=>x _; apply (mxlinear_continuous lf). Qed.

Lemma mxscalar_continuous m n (f : 'M[C]_(m,n) -> C) :
  scalar f -> continuous f.
Proof.
move: f; case: m=>[|m]; last first. case: n=>[|n]; last first.
all: move=>f Lf; set LfT : GRing.Linear.type _ _ :=
  HB.pack f (GRing.isLinear.Build _ _ _ _ f Lf);
have P0 : f = LfT by [].
suff: continuous LfT by [].
rewrite -linear_bounded_continuous -bounded_funP=>r/=.
have Pu : exists c, forall i j, `|LfT (delta_mx i j)| <= c.
exists (\sum_i\sum_j`|LfT (delta_mx i j)|)=>i j.
rewrite (bigD1 i)//= (bigD1 j)//= -addrA lerDl addr_ge0//.
1,2: rewrite sumr_ge0//. move=>k _. rewrite sumr_ge0//.
move: Pu=>[c Pc]. exists ((m.+1)%:R * ((n.+1)%:R * (r * c)))=>x/mxnorm_le_alter Pij.
(* have Pij i j : `|x i j| <= r by apply (le_trans (mx_norm_element _ (i,j))). *)
rewrite (matrix_sum_delta x) P0 linear_sum/=.
apply: (le_trans (ler_norm_sum _ _ _)). apply/ler_sum_const=>i.
rewrite P0 linear_sum/=.
apply: (le_trans (ler_norm_sum _ _ _)). apply/ler_sum_const=>j.
by rewrite P0 linearZ/= normrZ ler_pM//; move: (Pij (i,j)).
all: by apply: cst_continuous_eq; exists 0; apply/funext=>i; rewrite !mx_dim0 P0 linear0.
Qed.

Lemma mxcvgn_sfun m n (f : 'M[C]_(m,n) -> C)
  (u : nat -> 'M[C]_(m,n)) (a : 'M[C]_(m,n)) : 
  scalar f -> u @ \oo --> a -> (fun x=> f (u x)) @ \oo --> (f a).
Proof. by move/mxscalar_continuous=>P1; apply: continuous_cvg; apply: P1. Qed.

Lemma is_mxcvgn_sfun m n (f : 'M[C]_(m,n) -> C)
(u : nat -> 'M[C]_(m,n)) : scalar f -> cvgn u -> cvgn (f \o u).
Proof. by move=>P1; have := cvgP _ (mxcvgn_sfun P1 _); apply. Qed.

Lemma mxlimn_sfun m n (f : 'M[C]_(m,n) -> C)
  (u : nat -> 'M[C]_(m,n)) : 
  scalar f -> cvgn u -> limn (f \o u) = f (limn u).
Proof. move=>P1 ?; apply: cvg_lim => //. by apply: mxcvgn_sfun. Qed.

Lemma mxcclosed_comp m n (f : 'M[C]_(m,n) -> C)
  (A : set C) :
  scalar f -> closed A -> closed (f @^-1` A).
Proof. by move=>lf; apply closed_comp=>x _; apply (mxscalar_continuous lf). Qed.

Lemma mxcopen_comp m n (f : 'M[C]_(m,n) -> C)
  (A : set C) :
  scalar f -> open A -> open (f @^-1` A).
Proof. by move=>lf; apply open_comp=>x _; apply (mxscalar_continuous lf). Qed.

End MxLinearContinuous.

Section MxNormExtNumND.
Variable (R: realType) (C: extNumType R) (m n : nat).
Local Notation M := 'M[C]_(m.+1,n.+1).
Variable (mnorm : vnorm M).

Lemma compact_mxnorm_le (c : C) : compact [set x : M | `|x| <= c].
Proof.
pose A (i : 'I_(m.+1 * n.+1)) := [set x : C | `|x| <= c].
rewrite (_ : mkset _ = (@vec_mx C m.+1 n.+1) @` [set x : 'rV__ | forall i, A i (x ord0 i)]).
apply: continuous_compact.
apply: continuous_subspaceT=>x ?; apply: vec_mx_continuous.
apply: rV_compact=>i. apply: extNum_bounded_compact.
rewrite predeqE=>x/=; split; last first.
move=>[y Py]<-. apply/mxnorm_le_alter=>i. move: (Py (mxvec_index i.1 i.2)).
by rewrite/A/= -[vec_mx _ _ _]mxvecE vec_mxK.
move=>/mxnorm_le_alter Px; exists (mxvec x)=>[i|]; rewrite ?mxvecK//.
by case/mxvec_indexP: i=>i j; rewrite/A/= mxvecE; move: (Px (i,j)).
Qed.

Lemma compact_mxnorm_eq1 : compact [set x : M | `|x| = 1].
Proof.
suff P1: compact [set x : M | `|x| <= 1].
apply: (subclosed_compact _ P1 _).
apply: closed_mxnorm_sphere.
by move=>t; rewrite/==>->.
exact: compact_mxnorm_le.
Qed.

Lemma compact_mxnorm_eq1_vint : compact (mnorm @` [set x : M | `|x| = 1%:R]).
Proof.
apply continuous_compact; last by apply compact_mxnorm_eq1.
apply/continuous_subspaceT=>x ?; apply continuous_mnorm_ND.
Qed.

Lemma mnorm_lbounded_ND : exists2 c : C, 0 < c & forall x,  c * `|x| <= mnorm x.
Proof.
have sr : [set mnorm x | x in [set x | `|x| = 1%:R]] `<=` [set` Num.real].
by move=>x/=[y _]<-; rewrite normv_real.
move: (extNum_compact_min sr compact_mxnorm_eq1_vint (mxnorm_sphere_neq0_vint mnorm))
  =>[c [v /= Pv1 Pv2] Py].
have Pc: 0 < c by rewrite -Pv2 normv_gt0 -normr_gt0 Pv1 ltr01.
exists c=>// x; case E: (x == 0).
move: E=>/eqP ->. by rewrite normr0 normv0 mulr0.
have E1: `|x| > 0 by rewrite normr_gt0 E.
rewrite -{2}(scale1r x) -(@mulfV _ `|x|); last by move: E1; rewrite lt_def=>/andP[->].
rewrite -scalerA normvZ normr_id mulrC. apply ler_pM=>//.
by apply ltW. apply Py. exists (`|x|^-1 *: x)=>//.
rewrite mx_normZ ger0_norm ?inv_nng_ge0// mulVf//.
by move: E1; rewrite lt_def=>/andP[->].
Qed.

End MxNormExtNumND.

Section MxNormExtNumEqual.
Variable (R: realType) (C: extNumType R) (m n : nat).
Local Notation M := 'M[C]_(m,n).
Variable (mnorm : vnorm M).

Lemma mxlimn_mnorm (f : M ^nat) : 
  cvgn f -> limn (mnorm \o f) = mnorm (limn f).
Proof. by move=> ?; apply: cvg_lim => //; apply: mxcvgn_mnorm. Qed.

Lemma mnorm_lbounded : exists2 c : C, 
  0 < c & forall x,  c * mx_norm x <= mnorm x.
Proof.
case: m mnorm=>[mnorm'|m']; last case: n=>[mnorm'|n' mnorm'].
1,2: by exists 1=>// x; rewrite mx_dim0 !normv0 mul1r.
exact: mnorm_lbounded_ND.
Qed.

Let cl := projT1 (cid2 mnorm_lbounded).
Let cl_gt0 : cl > 0.
Proof. by move: (projT2 (cid2 mnorm_lbounded))=>[]. Qed.
Let clP : forall x, cl * mx_norm x <= mnorm x.
Proof. by move: (projT2 (cid2 mnorm_lbounded))=>[]. Qed.
Let clPV : forall x, mx_norm x <= mnorm x / cl.
Proof. by move=>x; rewrite ler_pdivlMr// mulrC. Qed.

Lemma compact_mnorm_le (y : C) : compact [set x : M | mnorm x <= y].
Proof.
suff P: compact [set x : M | mx_norm x <= y / cl].
apply: (subclosed_compact _ P _). apply: closed_mnorm_le.
by move=>z/= P1; move: (le_trans (clP _) P1); rewrite -ler_pdivlMl//= mulrC.
case: m mnorm=>[mnorm'|m']; last case: n=>[mnorm'|n' mnorm']; last exact: compact_mxnorm_le.
1,2: by apply: mx_set_compact_trivial; rewrite eqxx.
Qed.

Lemma compact_mnorm_sphere (y : C) : compact [set x : M | mnorm x = y].
Proof.
suff P1: compact [set x : M | mnorm x <= y].
apply: (subclosed_compact _ P1 _).
apply: closed_mnorm_sphere.
by move=>t; rewrite/==>->.
exact: compact_mnorm_le.
Qed.

Lemma Bolzano_Weierstrass (f : nat -> 'M[C]_(m,n)) (M : C) :
  (forall n, mx_norm (f n) <= M) -> exists (h: nat -> nat), 
    (forall n, (h n.+1 > h n)%N) /\ cvgn (f \o h).
Proof.
case: m f. move=>f _; exists id; split=>//. exact: is_mxcvgn_dim0n.
case: n. move=>n' f _; exists id; split=>//; exact: is_mxcvgn_dimn0.
move=>n' m' f P1; move: (@compact_mxnorm_le _ C m' n' M)=>P2.
apply: (@cluster_subsvg _ _ _ f _ P2 _)=>[x|i//=].
by move=>/extNum_ltr_add_invr[k Pk]; exists k; move: Pk; rewrite add0r.
by rewrite /normr/=.
Qed.

(* bounded seq: cvgn <-> any cvgn subseq to a *)
Lemma mxcvgn_subseqP_cvgn (f : nat -> 'M[C]_(m,n)) (a : 'M[C]_(m,n)) (M : C): 
  (forall n, mx_norm (f n) <= M) ->
  f @ \oo --> a <-> (forall (h: nat -> nat), (forall n, (h n.+1 > h n)%N) 
    -> cvgn (f \o h) -> limn (f \o h) = a).
split.
move=>/mxcvgn_subseqP + h Ph _. move=>/(_ h Ph).
apply: cvg_lim. apply mxhausdorff.
move=>P. apply contrapT. rewrite mxcvgn_subseqPN.
rewrite -forallNP=> e. rewrite -forallNP=> h.
rewrite -!implyNE=>Ph Pe Pc.
have P1: forall n0 : nat, mx_norm ((f \o h) n0) <= M by move=>n0; apply H.
move: (Bolzano_Weierstrass P1)=>[h' [Ph']]. rewrite -compA=>Pc'.
have P2: ~ ((f \o (h \o h')) @ \oo --> a).
rewrite mxcvgn_subseqPN; exists e; exists id; do 2 split=>//.
move=>n'; apply Pc.
apply P2. rewrite mxcvgn_limnE; split=>[|//].
apply P=>[|//]. move=>n'/=. by apply nchain_mono.
Qed.

End MxNormExtNumEqual.

Section MxNormExtNumEqual2.
Variable (R: realType) (C : extNumType R) (m n : nat).
Local Notation M := 'M[C]_(m,n).
Implicit Type (mnorm : vnorm M).

Lemma mnorm_bounded mnorm1 mnorm2 :
  exists2 c : C, 0 < c & forall x : M, mnorm1 x <= c * mnorm2 x.
Proof.
move: (mnorm_ubounded mnorm1)=>/=[c1 Pc1 P1].
move: (mnorm_lbounded mnorm2)=>/=[c2 Pc2 P2].
exists (c1 / c2)=>[|x]; first by apply Num.Theory.divr_gt0.
apply (le_trans (P1 x)). 
by rewrite -mulrA Num.Theory.ler_pM2l// Num.Theory.ler_pdivlMl.
Qed.

Lemma mxcauchy_seqv_eq mnorm1 mnorm2 (f : nat -> M) :
  cauchy_seqv mnorm1 f -> cauchy_seqv mnorm2 f.
Proof.
move: (mnorm_bounded mnorm2 mnorm1)=> [c Pc le_mn] P e Pe.
have Pec: 0 < (e / c) by apply divr_gt0.
move: (P (e/c) Pec )=>[N PN]; exists N=>s t Ps Pt.
apply: (le_lt_trans (le_mn (f s - f t))).
move: (PN s t Ps Pt); by rewrite ltr_pdivlMr// mulrC.
Qed.

Lemma mxcauchy_seqvE mnorm1 mnorm2 (f : nat -> M) :
  cauchy_seqv mnorm1 f <-> cauchy_seqv mnorm2 f.
Proof. split; by apply: mxcauchy_seqv_eq. Qed.

Lemma mxcauchy_seqE mnorm (f : nat -> M) :
  cauchy_seqv mnorm f <-> mxcauchy_seq f.
Proof. split; by apply: mxcauchy_seqv_eq. Qed.

Lemma mxcauchy_seqvP mnorm (f : nat -> M) :
  cauchy_seqv mnorm f <-> cvgn f.
Proof. by rewrite mxcauchy_seqE; apply: mxcauchy_seqP. Qed.

End MxNormExtNumEqual2.

Module MxCPorder.

Section Definitions.
Variables (R: realType) (C : extNumType R) (m n : nat).
Variable (disp: unit) (B : POrder.axioms_ disp 'M[C]_(m,n)).
Local Notation M := 'M[C]_(m,n).
Local Notation "x '⊑' y" := (@Order.le disp (@POrder.Pack disp M B) x y) 
  (at level 70, y at next level).

Structure mxcporder := MxCPorder {
  _ : forall (z x y : M), x ⊑ y -> x + z ⊑ y + z;
  _ : forall (e : C) (x y : M), 0 < e -> x ⊑ y -> e *: x ⊑ e *: y;
  _ : closed [set x : M | (0 : M) ⊑ x];
}.

End Definitions.

Module Import Exports.
Notation mxcporder B disp:= (@mxcporder _ _ _ _ disp B).
Notation MxCPorder := MxCPorder.
(* Coercion mnorm : cmxnormcvg >-> vnorm.
Notation "[ 'cmxnormcvg' 'of' f ]" := (@clone_vnormcvg _ _ _ _ _ f _ id _ _ _ _ id)
  (at level 0, format"[ 'cmxnormcvg'  'of'  f ]") : form_scope. *)
End Exports.

Module Theory.

Section Property.
Import Num.Def Num.Theory.
Variable (R: realType) (C: extNumType R) (m n : nat).
Local Notation M := 'M[C]_(m,n).
Variable (disp: unit) (B : POrder.axioms_ disp 'M[C]_(m,n)).
Variable (mxorder : mxcporder B disp).

Local Notation "x '⊏' y" := (@Order.lt disp (@POrder.Pack disp M B) x y) (at level 70, y at next level).
Local Notation "x '⊑' y" := (@Order.le disp (@POrder.Pack disp M B) x y) (at level 70, y at next level).
Notation "'ubounded_by' b f" := (forall i, f i ⊑ b) (at level 10, b, f at next level).
Notation "'lbounded_by' b f" := (forall i, b ⊑ f i) (at level 10, b, f at next level).
Notation "'mxnondecreasing_seq' f" := ({homo f : n m / (n <= m)%nat >-> (n ⊑ m)})
  (at level 10).
Notation "'mxnonincreasing_seq' f" := ({homo f : n m / (n <= m)%nat >-> (m ⊑ n)})
  (at level 10).

Lemma lemx_add2r (z x y : M) : x ⊑ y -> x + z ⊑ y + z.
Proof. by move: z x y; case: mxorder. Qed.
Lemma lemx_pscale2lP (e : C) (x y : M) : 0 < e -> x ⊑ y -> e *: x ⊑ e *: y.
Proof. by move: e x y; case: mxorder. Qed.
Lemma lemx_pscale2l: forall (e : C) (x y : M), 0 < e -> x ⊑ y = (e *: x ⊑ e *: y).
Proof. 
move=> e x y egt0. apply/Bool.eq_true_iff_eq.
split. by apply lemx_pscale2lP. rewrite -{2}(scale1r x) -{2}(scale1r y) -(@mulVf _ e).
rewrite -!scalerA. apply lemx_pscale2lP. rewrite invr_gt0//. by apply/lt0r_neq0.
Qed.
Lemma closed_gemx0: closed [set x : M | (0 : M) ⊑ x].
Proof. by case: mxorder. Qed.

Implicit Type (u v : M^nat).

Lemma submx_ge0 (x y : M) : ((0 : M) ⊑ x - y) = (y ⊑ x).
Proof. 
apply/Bool.eq_iff_eq_true; split=>[/(@lemx_add2r y)|/(@lemx_add2r (-y))];
by rewrite ?addrNK ?add0r// addrN.
Qed.

Lemma lemx_opp2 : {mono (-%R : M -> M) : x y /~ x ⊑ y }.
Proof. by move=>x y; rewrite -submx_ge0 opprK addrC submx_ge0. Qed.

Lemma mxnondecreasing_opp u :
  mxnondecreasing_seq (- u) = mxnonincreasing_seq u.
Proof. by rewrite propeqE; split => du x y /du; rewrite lemx_opp2. Qed.

Lemma mxnonincreasing_opp u :
  mxnonincreasing_seq (- u) = mxnondecreasing_seq u.
Proof. by rewrite propeqE; split => du x y /du; rewrite lemx_opp2. Qed.

Lemma mxlbounded_by_opp (b : M) u :
  lbounded_by (-b) (- u) = ubounded_by b u.
Proof. 
by rewrite propeqE; split => bu i; move: (bu i); 
  rewrite {2}/GRing.opp/= lemx_opp2.
Qed.

Lemma mxubounded_by_opp (b : M) u :
  ubounded_by (-b) (- u) = lbounded_by b u.
Proof. 
by rewrite propeqE; split => bu i; move: (bu i); 
  rewrite {2}/GRing.opp/= lemx_opp2.
Qed.

(* different canonical route. prevent eq_op porderType ringType *)
Lemma ltmx_def (x y : M) : (x ⊏ y) = (y != x) && (x ⊑ y).
Proof.
rewrite lt_def; congr (~~ _ && _); apply/Bool.eq_iff_eq_true.
split=>/eqP/=->; by rewrite eqxx.
Qed.

Lemma submx_gt0 (x y : M) : ((0 : M) ⊏ y - x) = (x ⊏ y).
Proof. by rewrite !ltmx_def submx_ge0 subr_eq0. Qed.

Lemma mxopen_nge0 : open [set x : M | ~ (0 : M) ⊑ x].
Proof. rewrite openC; apply closed_gemx0. Qed.

Lemma mxopen_nge y :  open [set x : M | ~ y ⊑ x].
Proof.
move: (@mxaddr_continuous _ C m n (-y))=>/continuousP/=/(_ _ mxopen_nge0).
suff ->: [set x : M | ~ y ⊑ x] = [set t | [set x | ~ (0 : M) ⊑ x] (- y + t)] by [].
by apply/funext=>x; rewrite /= addrC submx_ge0.
Qed.

Lemma mxopen_nle0 : open [set x : M | ~ x ⊑ (0 : M)].
Proof.
move: (@mxopp_continuous R C m n)=>/continuousP/=/(_ _ mxopen_nge0).
suff ->: [set x | ~ x ⊑ (0 : M)] = [set t | [set x | ~ (0 : M) ⊑ x] (- t)] by [].
by apply/funext=>x; rewrite /= -{2}oppr0 lemx_opp2. 
Qed.

Lemma mxopen_nle y :  open [set x : M | ~ x ⊑ y].
Proof.
move: (@mxopp_continuous R C m n)=>/continuousP/=/(_ _ (@mxopen_nge (-y))).
suff ->: [set x : M | ~ x ⊑ y] = [set t | [set x : M | ~ - y ⊑ x] (- t)] by [].
by apply/funext=>x; rewrite /= lemx_opp2.
Qed.

Lemma mxclosed_ge (x : M) : closed [set y : M | x ⊑ y ].
Proof. 
set A := ~` [set y : M | ~ (x ⊑ y)].
have ->: (fun x0 : 'M_(m, n) => is_true (x ⊑ x0)) = A.
by rewrite predeqE /A => y/=; rewrite notK.
rewrite closedC. apply/mxopen_nge. 
Qed.

Lemma mxclosed_le (x : M) : closed [set y : M | y ⊑ x ].
Proof. 
set A := ~` [set y : M | ~ (y ⊑ x)].
have ->: (fun x0 : 'M_(m, n) => is_true (x0 ⊑ x)) = A.
by rewrite predeqE /A => y/=; rewrite notK.
rewrite closedC. apply/mxopen_nle. 
Qed.

Lemma mxlimn_ge_near (x : M) (u : M ^nat) : 
  cvgn u -> (\forall n \near \oo, x ⊑ u n) -> x ⊑ limn u.
Proof.
move=> /[swap] /(closed_cvg ((@Order.le disp (@POrder.Pack disp M B) x)))/= P1;
apply P1. apply: mxclosed_ge.
Qed.

Lemma mxlimn_le_near (x : M) (u : M ^nat) : 
  cvgn u -> (\forall n \near \oo, u n ⊑ x) -> limn u ⊑ x.
Proof.
move=> /[swap] /(closed_cvg (fun y =>(@Order.le disp (@POrder.Pack disp M B) y x)))/= P1;
apply P1. apply: mxclosed_le.
Qed.

Lemma ler_mxlimn_near (u_ v_ : M ^nat) : cvgn u_ -> cvgn v_ ->
  (\forall n \near \oo, u_ n ⊑ v_ n) -> limn u_ ⊑ limn v_.
Proof.
move=> uv cu cv; rewrite -(submx_ge0) -mxlimnB.
apply: mxlimn_ge_near. apply: is_mxcvgnB.
3: by apply: filterS cv => k; rewrite (submx_ge0).
1,3: by []. all: apply uv.
Qed.

Lemma mxlimn_ge (x : M) (u : M ^nat) : cvgn u -> lbounded_by x u -> x ⊑ limn u.
Proof. by move=>P1 P2; apply: (mxlimn_ge_near P1); apply: nearW. Qed.

Lemma mxlimn_le (x : M) (u : M ^nat) : cvgn u -> ubounded_by x u -> limn u ⊑ x.
Proof. by move=>P1 P2; apply: (mxlimn_le_near P1); apply: nearW. Qed.

Lemma ler_mxlimn (u v : M^nat) : cvgn u -> cvgn v ->
  (forall n, u n ⊑ v n) -> limn u ⊑ limn v.
Proof. by move=>P1 P2 P3; apply: (ler_mxlimn_near P1 P2); apply: nearW. Qed.

Lemma mxnondecreasing_cvgn_le (u : M ^nat) :
       mxnondecreasing_seq u -> cvgn u -> ubounded_by (limn u) u.
Proof. move=>Ph Pc i; apply: mxlimn_ge_near=>//; exists i=>// j; apply Ph. Qed.

Lemma mxnonincreasing_cvgn_ge (u : M ^nat) : 
  mxnonincreasing_seq u -> cvgn u -> lbounded_by (limn u) u.
Proof. move=>Ph Pc i; apply: mxlimn_le_near=>//; exists i=>// j; apply Ph. Qed.

Lemma nchain_mono1 (h: nat -> nat) :
  (forall n, (h n.+1 > h n)%N) -> forall n m, (n <= m)%N -> (h n <= h m)%N.
Proof.
move=>P1 n' m'; rewrite leq_eqVlt=>/orP[/eqP->//|P2].
by apply/ltnW/nchain_mono.
Qed.

Lemma le0x_mxZ (X Y : M) a : ((0 : M) ⊑ X) && (X ⊑ Y) -> 0 < a < 1 ->
  ((0 : M) ⊑ a*:X) && (a*:X ⊑ Y).
Proof.
move=>/andP[P1 P2]/andP[P3]; rewrite -subr_gt0=>P4; apply/andP; split.
by move: (lemx_pscale2lP P3 P1); rewrite scaler0.
apply: (le_trans (lemx_pscale2lP P3 P2)).
move: (le_trans P1 P2)=>/(lemx_pscale2lP P4).
by rewrite scaler0 scalerBl scale1r=>/(lemx_add2r (a*:Y)); rewrite addrNK add0r.
Qed.

(*----------------------------------------------------------------------------*)
(* proof sketch : by contradiction                                            *)
(* define diverge seq c i := (i+1) * (1 + |Y|)                                *)
(* exists seq X i s.t. |X i| > c i                                            *)
(* seq (X i)/|X i| is bounded, so exists cvgn subseq (X \o h)                  *)
(* forall i, 0 <= (X \o h) i <= Y, so 0 <= limn (X \o h)                       *)
(* seq ((Y - X i)/|Y - X i| \o h) @ \oo --> - limn (X \o h)                          *)
(* but 0 <= (Y - X i)/|Y - X i| <= 1, so 0 <= - limn (X \o h)                  *)
(* note that |limn (X \o h)| = 1, so contradiction                             *)
(*----------------------------------------------------------------------------*)
Lemma porder_mxnorm_bound (Y : M) : exists c, c > 0 /\ 
  (forall X, ((0 : M) ⊑ X) && (X ⊑ Y) -> c * mx_norm X <= mx_norm Y).
Proof.
case E: (Y == 0); first by move/eqP: E=>->; exists 1; split=>// x; 
  rewrite -eq_le=>/eqP<-; rewrite normv0 mulr0.
have Q1: mx_norm Y > 0 by rewrite normv_gt0 E.
pose c i := i.+1%:R * (1 + mx_norm Y).
have cinc i : c i >= 1 + mx_norm Y by rewrite/c ler_pMl ?addr_gt0// ler1Sn.
have Q2 i : c i > i.+1%:R by rewrite/c ltr_pMr// ltrDl.
have Q3 i : c i > 0 by rewrite /c mulr_gt0// addr_gt0.
have Q4 i : 0 < mx_norm Y / c i by rewrite divr_gt0.
rewrite not_existsP=>P1.
have P2 i: {X : M | ((0 : M) ⊑ X) && (X ⊑ Y) /\ (mx_norm X > c i)}.
  apply/cid; move: (P1 (mx_norm Y/c i)); rewrite -implyNE=>/(_ (Q4 i)).
  rewrite not_existsP; apply contra_not=>P2 x P3; move: (P2 x).
  rewrite -implyNE=>/(_ P3)/negP; rewrite -mulrA ger_pMr// ler_pdivrMl//.
  by rewrite mulr1 real_leNgt// ger0_real// ?normv_ge0//; apply/ltW.
pose x i := projT1 (P2 i).
have P7 i : ((0 : M) ⊑ x i) && (x i ⊑ Y) by move: (projT2 (P2 i))=>[].
have P4 i : c i < mx_norm (x i) by move: (projT2 (P2 i))=>[].
have P5 i : 0 < mx_norm (x i) by apply: (lt_trans _ (P4 _)).
pose nx i := (mx_norm (x i))^-1 *: (x i).
have norm_nx i : mx_norm (nx i) = 1.
  by rewrite /nx normvZ/= gtr0_norm ?mulVf// ?invr_gt0//; apply: lt0r_neq0.
have bound_nx i : mx_norm (nx i) <= 1 by rewrite norm_nx.
move: (Bolzano_Weierstrass bound_nx)=>[h [mn]].
move: (nchain_ge mn)=>hgen.
set y := nx \o h=>Cy; pose ly := limn y : M.
have cy : y @ \oo --> ly by [].
have P3 i : ((0 : M) ⊑ y i) && (y i ⊑ Y).
  rewrite /y/=/nx; apply/le0x_mxZ=>//.
  rewrite invr_gt0 invf_lt1// P5/=; apply: (lt_trans _ (P4 _)).
  by apply: (le_lt_trans _ (Q2 _)); rewrite -addn1 natrD lerDr.
have ly_ge0: ((0 : M) ⊑ ly) by apply: mxlimn_ge=>[//|i]; move: (P3 i)=>/andP[].
have Q5 i: mx_norm (Y - x i) > i.+1%:R.
  rewrite addrC;
  move: (@levB_normD _ _ mx_norm_vnorm (- x i) Y)=>/=.
  apply: lt_le_trans; rewrite mx_normN ltrBrDl.
  apply: (le_lt_trans _ (P4 _)); rewrite addrC/c mulrDr.
  by rewrite mulr1 lerD2l ler_pMl// ler1Sn.
have Q6 i: mx_norm (Y - x i) > 0 by apply: (lt_trans _ (Q5 _)).
pose nnx i := (mx_norm (Y - x (h i)))^-1 *: (Y - x (h i)).
pose nnx1 i := (mx_norm (Y - x (h i)))^-1 *: Y.
pose nnx2 i := (mx_norm (Y - x (h i)))^-1 * mx_norm (x (h i)).
have: nnx @ \oo --> 0 - 1 *: ly.
  have ->: nnx = nnx1 - (fun i=>nnx2 i *: y i).
    apply/funext=>i; rewrite/nnx/nnx1 {3}/GRing.add/={4}/GRing.opp/=/nnx2/nx.
    by rewrite scalerA -mulrA mulfV ?mulr1 ?scalerBr// lt0r_neq0.
  have Q7 e: 0 < e -> exists N : nat, forall i : nat, (N <= i)%N -> 
    mx_norm Y / (mx_norm (Y - x (h i))) < e.
    move=>egt0; have /extNum_archi: e / mx_norm Y > 0 by rewrite divr_gt0.
    move=>[k Pk]; exists k=>i Pi; rewrite/=mulrC -ltr_pdivlMr//.
    apply: (le_lt_trans _ Pk); rewrite lef_pV2 ?posrE//; apply/ltW.
    by apply: (le_lt_trans _ (Q5 _)); rewrite ler_nat ltnS; apply: (leq_trans Pi).
  apply mxcvgnB. 2: apply mxcvgnZ=>[|//].
  apply/mxcvgn_seqP=>e egt0; move: (Q7 e egt0)=>[k Pk]; exists k=>i/Pk.
  by rewrite add0r mx_normN/nnx1 normvZ/= gtr0_norm ?invr_gt0// mulrC.
  apply cvgn_seqP=>e egt0; move: (Q7 e egt0)=>[k Pk]; exists k=>i/Pk.
  rewrite ltr_pdivrMr// =>P6.
  rewrite/nnx2 -(@mulfV _ (mx_norm (Y - x (h i))) _); last by apply/lt0r_neq0.
  rewrite mulrC -mulrBr normrM gtr0_norm ?ltr_pdivrMl// ?invr_gt0// mulrC.
  by apply: (le_lt_trans _ P6); rewrite -[mx_norm (x (h i))]normvN/= 
    -{2}[Y](addrNK (x (h i))) -{4}(opprK (x (h i))); apply: lev_dist_dist.
rewrite scale1r add0r=>cny.
have Cny: cvgn nnx by apply/cvg_ex; exists (-ly). 
have nly_ge0: ((0 : M) ⊑ - ly).
  rewrite -(cvg_lim _ cny); last by apply mxhausdorff.
  apply: mxlimn_ge=>[//|i].
  suff: ((0 : M) ⊑ nnx i) && (nnx i ⊑ Y) by move=>/andP[].
  rewrite /nnx; apply/le0x_mxZ; apply/andP; split.
  rewrite submx_ge0. 2: rewrite -submx_ge0 opprB addrC addrNK.
  1,2: by move: (P7 (h i))=>/andP[].
  rewrite invr_gt0//. rewrite invf_lt1//; apply/(le_lt_trans _ (Q5 _))/ler1Sn.
have : mx_norm ly = 1.
  rewrite -(mxlimn_mnorm mx_norm_vnorm Cy)=>/=.
  suff ->: mx_norm (n:=n) \o y = fun=>1 by apply/lim_cst/ethausdorff.
  by apply/funext=>i; rewrite/=/y//=.
have: ((0 : M) ⊑ ly) && (ly ⊑ 0) by rewrite ly_ge0/= -submx_ge0 add0r.
by rewrite -eq_le eq_sym=>/eqP->/eqP; rewrite normv0 eq_sym oner_eq0.
Qed.

Lemma bounded_mxnorm (bl br : M) u :
  lbounded_by bl u -> ubounded_by br u -> 
  exists c : C, forall n, mx_norm (u n) <= c.
Proof.
move: (porder_mxnorm_bound (br-bl))=>[c [Pc P]] Pl Pr.
exists (mx_norm (br - bl) / c + mx_norm bl)=>i.
rewrite -[u i](addrNK bl). apply: (le_trans (ler_mx_norm_add _ _)).
rewrite lerD2r ler_pdivlMr// mulrC P//; apply/andP; split.
by rewrite submx_ge0. by apply lemx_add2r.
Qed.

Lemma mxnondecreasing_is_cvgn (f : nat -> M) (b : M) :
  mxnondecreasing_seq f -> ubounded_by b f -> cvgn f.
move=>P1 P2.
have P3: lbounded_by (f 0%N) f by move=>i; by apply/P1.
move: (bounded_mxnorm P3 P2)=>[c Pc].
move: (Bolzano_Weierstrass Pc)=>[h0 [Ph0 cvgh0]].
apply/cvg_ex. exists (limn (f \o h0)).
apply/(mxcvgn_subseqP_cvgn (limn (f \o h0)) Pc)=>h1 Ph1 cvgh1.
suff: (limn (f \o h1) ⊑ limn (f \o h0)) && (limn (f \o h0) ⊑ limn (f \o h1)).
by rewrite -eq_le=>/eqP.
apply/andP; split; apply: (mxlimn_le)=>[|i].
2: have P4: (f \o h1) i ⊑ (f \o h0) (h1 i) by apply/P1/nchain_ge.
4: have P4: (f \o h0) i ⊑ (f \o h1) (h0 i) by apply/P1/nchain_ge.
2,4: apply: (le_trans P4 _); apply (mxnondecreasing_cvgn_le).
1,5: apply cvgh1. 2,4: apply cvgh0.
all: by move=>x y Pxy; apply P1; apply/nchain_mono1.
Qed.

Lemma mxnonincreasing_is_cvgn (f : nat -> M) (b : M) :
    mxnonincreasing_seq f -> lbounded_by b f -> cvgn f.
Proof.
rewrite -(mxnondecreasing_opp) -(mxubounded_by_opp) -is_mxcvgnNE.
exact: mxnondecreasing_is_cvgn.
Qed.

End Property.

End Theory.
End MxCPorder.

Export MxCPorder.
Export MxCPorder.Exports.
Export MxCPorder.Theory.

End ExtNumTopology.

Import ExtNumTopology.

(* FinNormedModType *)
#[short(type="finNormedModType")]
HB.structure Definition FinNormedModule (C : numDomainType) :=
  { T of NormedModule C T & Lmodule_hasFinDim C T }.

Module FinNormedModuleExports.
#[deprecated(since="mathcomp 2.0.0", note="Use FinNormedModule.clone instead.")]
Notation "[ 'finNormedModType' C 'of' T 'for' cT ]" := (FinNormedModule.clone C T%type cT)
  (at level 0, format "[ 'finNormedModType'  C  'of'  T  'for'  cT ]") : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use FinNormedModule.clone instead.")]
Notation "[ 'finNormedModType' C 'of' T ]" := (FinNormedModule.clone C T%type _)
  (at level 0, format "[ 'finNormedModType'  C  'of'  T ]") : form_scope.
End FinNormedModuleExports.
HB.export FinNormedModuleExports.

HB.mixin Record FinNormedModule_isVOrderFinNormedModule (R : numFieldType) V of
  FinNormedModule R V & VOrder R V := {
    closed_gev0 : closed [set x : V | (le 0 x)] ;
  }.

Module VOrderFinNormedModule.

Section ClassDef.

Record axioms_ (R : numFieldType) (T : Type) : Type := Class {
  classical_sets_isPointed_mixin : isPointed.axioms_ T;
  topology_selfFiltered_mixin : selfFiltered.axioms_ T;
  topology_isFiltered_mixin : isFiltered.axioms_ T T;
  GRing_isNmodule_mixin : GRing.isNmodule.axioms_ T;
  choice_hasChoice_mixin : hasChoice.axioms_ T;
  eqtype_hasDecEq_mixin : Equality.mixin_of T;
  topology_Nbhs_isUniform_mixin_mixin : 
    Nbhs_isUniform_mixin.axioms_ T classical_sets_isPointed_mixin
      choice_hasChoice_mixin eqtype_hasDecEq_mixin
      topology_selfFiltered_mixin topology_isFiltered_mixin;
  topology_Nbhs_isTopological_mixin : 
    Nbhs_isTopological.axioms_ T classical_sets_isPointed_mixin
      choice_hasChoice_mixin eqtype_hasDecEq_mixin
      topology_selfFiltered_mixin topology_isFiltered_mixin;
  topology_Uniform_isPseudoMetric_mixin : 
    Uniform_isPseudoMetric.axioms_ R T classical_sets_isPointed_mixin
      choice_hasChoice_mixin eqtype_hasDecEq_mixin 
      topology_selfFiltered_mixin topology_isFiltered_mixin
      topology_Nbhs_isUniform_mixin_mixin topology_Nbhs_isTopological_mixin;
  GRing_Nmodule_isZmodule_mixin : 
    GRing.Nmodule_isZmodule.axioms_ T GRing_isNmodule_mixin
      choice_hasChoice_mixin eqtype_hasDecEq_mixin;
  Num_Zmodule_isNormed_mixin : 
    Num.Zmodule_isNormed.axioms_ R T GRing_isNmodule_mixin
      choice_hasChoice_mixin eqtype_hasDecEq_mixin GRing_Nmodule_isZmodule_mixin;
  normedtype_NormedZmod_PseudoMetric_eq_mixin : 
    NormedZmod_PseudoMetric_eq.axioms_ R T GRing_isNmodule_mixin
      classical_sets_isPointed_mixin choice_hasChoice_mixin
      eqtype_hasDecEq_mixin GRing_Nmodule_isZmodule_mixin
      Num_Zmodule_isNormed_mixin topology_selfFiltered_mixin
      topology_isFiltered_mixin topology_Nbhs_isUniform_mixin_mixin
      topology_Nbhs_isTopological_mixin topology_Uniform_isPseudoMetric_mixin;
  GRing_Zmodule_isLmodule_mixin : 
    GRing.Zmodule_isLmodule.axioms_ R T GRing_isNmodule_mixin
      choice_hasChoice_mixin eqtype_hasDecEq_mixin GRing_Nmodule_isZmodule_mixin;
  normedtype_PseudoMetricNormedZmod_Lmodule_isNormedModule_mixin : 
    PseudoMetricNormedZmod_Lmodule_isNormedModule.axioms_ R T
      classical_sets_isPointed_mixin topology_selfFiltered_mixin
      topology_isFiltered_mixin GRing_isNmodule_mixin choice_hasChoice_mixin
      eqtype_hasDecEq_mixin topology_Nbhs_isTopological_mixin
      topology_Nbhs_isUniform_mixin_mixin
      topology_Uniform_isPseudoMetric_mixin GRing_Nmodule_isZmodule_mixin
      Num_Zmodule_isNormed_mixin normedtype_NormedZmod_PseudoMetric_eq_mixin
      GRing_Zmodule_isLmodule_mixin;
  vector_Lmodule_hasFinDim_mixin : 
    Vector.mixin_of R T GRing_isNmodule_mixin 
      choice_hasChoice_mixin eqtype_hasDecEq_mixin 
      GRing_Nmodule_isZmodule_mixin GRing_Zmodule_isLmodule_mixin;
  Order_isPOrder_mixin : isPOrder.axioms_ ring_display T
                           eqtype_hasDecEq_mixin;
  mxpred_POrderedLmodule_isVOrder_mixin : 
    POrderedLmodule_isVOrder.axioms_ R T GRing_isNmodule_mixin
      choice_hasChoice_mixin eqtype_hasDecEq_mixin
      GRing_Nmodule_isZmodule_mixin GRing_Zmodule_isLmodule_mixin
      Order_isPOrder_mixin;
  extnum_FinNormedModule_isVOrderFinNormedModule_mixin : 
    FinNormedModule_isVOrderFinNormedModule.axioms_ R T
      classical_sets_isPointed_mixin topology_selfFiltered_mixin 
      topology_isFiltered_mixin GRing_isNmodule_mixin choice_hasChoice_mixin
      eqtype_hasDecEq_mixin topology_Nbhs_isTopological_mixin 
      topology_Nbhs_isUniform_mixin_mixin topology_Uniform_isPseudoMetric_mixin
      GRing_Nmodule_isZmodule_mixin Num_Zmodule_isNormed_mixin
      normedtype_NormedZmod_PseudoMetric_eq_mixin GRing_Zmodule_isLmodule_mixin
      normedtype_PseudoMetricNormedZmod_Lmodule_isNormedModule_mixin
      vector_Lmodule_hasFinDim_mixin 
      Order_isPOrder_mixin mxpred_POrderedLmodule_isVOrder_mixin;
}.

Record type (R : numFieldType) : Type := Pack
  { sort : Type;  class : axioms_ R sort }.
#[reversible] Coercion sort : type >-> Sortclass.

Definition phant_on_ (R : numFieldType) (C : type R) (_ : phant C) := class C.
Definition phant_clone (R : numFieldType) (C : Type) (cT : type R) (c : axioms_ R C) :=
  fun _ : structures.unify Type Type C cT nomsg =>
  fun _ : structures.unify (type R) (type R) cT
          (@Pack R C c) nomsg => (@Pack R C c).

End ClassDef.

Notation copy A B := (phant_on_ (Phant B) : axioms_ _ A).
Notation on A := (phant_on_ (Phant _) : axioms_ _ A).
Notation clone A T B := (@phant_clone A T B _ id_phant id_phant).

End VOrderFinNormedModule.

(* short name *)
Notation vorderFinNormedModType := VOrderFinNormedModule.type.
#[reversible] Coercion VOrderFinNormedModule.sort : vorderFinNormedModType >-> Sortclass.

(* type.axioms_ >-> type.axioms_ reversible Coercion *)
Definition extnum_VOrderFinNormedModule_class__to__eqtype_Equality_class 
  (R : numFieldType) (C : Type) (c : VOrderFinNormedModule.axioms_ R C) :=
  Equality.Class (VOrderFinNormedModule.eqtype_hasDecEq_mixin c).
#[reversible] Coercion extnum_VOrderFinNormedModule_class__to__eqtype_Equality_class : 
  VOrderFinNormedModule.axioms_ >-> Equality.axioms_.

Definition extnum_VOrderFinNormedModule_class__to__choice_Choice_class 
  (R : numFieldType) (C : Type) (c : VOrderFinNormedModule.axioms_ R C) := 
  Choice.Class (VOrderFinNormedModule.choice_hasChoice_mixin c) 
    (VOrderFinNormedModule.eqtype_hasDecEq_mixin c).
#[reversible] Coercion extnum_VOrderFinNormedModule_class__to__choice_Choice_class: 
  VOrderFinNormedModule.axioms_ >-> Choice.axioms_.

Definition extnum_VOrderFinNormedModule_class__to__GRing_Nmodule_class 
  (R : numFieldType) (C : Type) (c : VOrderFinNormedModule.axioms_ R C) := 
  GRing.Nmodule.Class (VOrderFinNormedModule.GRing_isNmodule_mixin c) 
    (VOrderFinNormedModule.choice_hasChoice_mixin c)
    (VOrderFinNormedModule.eqtype_hasDecEq_mixin c).
#[reversible] Coercion extnum_VOrderFinNormedModule_class__to__GRing_Nmodule_class: 
  VOrderFinNormedModule.axioms_ >-> GRing.Nmodule.axioms_.

Definition extnum_VOrderFinNormedModule_class__to__GRing_Zmodule_class 
  (R : numFieldType) (C : Type) (c : VOrderFinNormedModule.axioms_ R C) := 
  GRing.Zmodule.Class (VOrderFinNormedModule.GRing_Nmodule_isZmodule_mixin c).
#[reversible] Coercion extnum_VOrderFinNormedModule_class__to__GRing_Zmodule_class: 
  VOrderFinNormedModule.axioms_ >-> GRing.Zmodule.axioms_.

Definition extnum_VOrderFinNormedModule_class__to__Num_NormedZmodule_class 
  (R : numFieldType) (C : Type) (c : VOrderFinNormedModule.axioms_ R C) := 
  Num.NormedZmodule.Class (VOrderFinNormedModule.Num_Zmodule_isNormed_mixin c).
#[reversible] Coercion extnum_VOrderFinNormedModule_class__to__Num_NormedZmodule_class: 
  VOrderFinNormedModule.axioms_ >-> Num.NormedZmodule.axioms_.

Definition extnum_VOrderFinNormedModule_class__to__Order_POrder_class
  (R : numFieldType) (C : Type) (c : VOrderFinNormedModule.axioms_ R C) := 
  POrder.Class (VOrderFinNormedModule.choice_hasChoice_mixin c)
  (VOrderFinNormedModule.Order_isPOrder_mixin c).
#[reversible] Coercion extnum_VOrderFinNormedModule_class__to__Order_POrder_class : 
  VOrderFinNormedModule.axioms_ >-> POrder.axioms_.

Definition extnum_VOrderFinNormedModule_class__to__Num_POrderedZmodule_class 
  (R : numFieldType) (C : Type) (c : VOrderFinNormedModule.axioms_ R C) := 
  Num.POrderedZmodule.Class (VOrderFinNormedModule.GRing_Nmodule_isZmodule_mixin c) 
  (VOrderFinNormedModule.Order_isPOrder_mixin c).
#[reversible] Coercion extnum_VOrderFinNormedModule_class__to__Num_POrderedZmodule_class : 
  VOrderFinNormedModule.axioms_ >-> Num.POrderedZmodule.axioms_.

Definition extnum_VOrderFinNormedModule_class__to__classical_sets_Pointed_class
  (R : numFieldType) (C : Type) (c : VOrderFinNormedModule.axioms_ R C) := 
  classical_sets.Pointed.Class (VOrderFinNormedModule.classical_sets_isPointed_mixin c) 
  (VOrderFinNormedModule.choice_hasChoice_mixin c)
  (VOrderFinNormedModule.eqtype_hasDecEq_mixin c).
#[reversible] Coercion extnum_VOrderFinNormedModule_class__to__classical_sets_Pointed_class : 
  VOrderFinNormedModule.axioms_ >-> Pointed.axioms_.

Definition extnum_VOrderFinNormedModule_class__to__topology_Filtered_class
  (R : numFieldType) (C : Type) (c : VOrderFinNormedModule.axioms_ R C) := 
  Filtered.Class (VOrderFinNormedModule.classical_sets_isPointed_mixin c) 
  (VOrderFinNormedModule.choice_hasChoice_mixin c)
  (VOrderFinNormedModule.eqtype_hasDecEq_mixin c)
  (VOrderFinNormedModule.topology_isFiltered_mixin c).
#[reversible] Coercion extnum_VOrderFinNormedModule_class__to__topology_Filtered_class : 
  VOrderFinNormedModule.axioms_ >-> Filtered.axioms_.

Definition extnum_VOrderFinNormedModule_class__to__topology_Nbhs_class
  (R : numFieldType) (C : Type) (c : VOrderFinNormedModule.axioms_ R C) := 
  Nbhs.Class (VOrderFinNormedModule.classical_sets_isPointed_mixin c) 
  (VOrderFinNormedModule.choice_hasChoice_mixin c)
  (VOrderFinNormedModule.eqtype_hasDecEq_mixin c)
  (VOrderFinNormedModule.topology_selfFiltered_mixin c)
  (VOrderFinNormedModule.topology_isFiltered_mixin c).
#[reversible] Coercion extnum_VOrderFinNormedModule_class__to__topology_Nbhs_class : 
  VOrderFinNormedModule.axioms_ >-> Nbhs.axioms_.

Definition extnum_VOrderFinNormedModule_class__to__topology_Topological_class
  (R : numFieldType) (C : Type) (c : VOrderFinNormedModule.axioms_ R C) := 
  Topological.Class (VOrderFinNormedModule.topology_Nbhs_isTopological_mixin c).
#[reversible] Coercion extnum_VOrderFinNormedModule_class__to__topology_Topological_class : 
  VOrderFinNormedModule.axioms_ >-> Topological.axioms_.

Definition extnum_VOrderFinNormedModule_class__to__topology_Uniform_class
  (R : numFieldType) (C : Type) (c : VOrderFinNormedModule.axioms_ R C) := 
  Uniform.Class (VOrderFinNormedModule.topology_Nbhs_isUniform_mixin_mixin c)
  (VOrderFinNormedModule.topology_Nbhs_isTopological_mixin c).
#[reversible] Coercion extnum_VOrderFinNormedModule_class__to__topology_Uniform_class : 
  VOrderFinNormedModule.axioms_ >-> Uniform.axioms_.

Definition extnum_VOrderFinNormedModule_class__to__topology_PseudoMetric_class
  (R : numFieldType) (C : Type) (c : VOrderFinNormedModule.axioms_ R C) := 
  PseudoMetric.Class (VOrderFinNormedModule.topology_Uniform_isPseudoMetric_mixin c).
#[reversible] Coercion extnum_VOrderFinNormedModule_class__to__topology_PseudoMetric_class : 
  VOrderFinNormedModule.axioms_ >-> PseudoMetric.axioms_.

Definition extnum_VOrderFinNormedModule_class__to__normedtype_PseudoMetricNormedZmod_class
  (R : numFieldType) (C : Type) (c : VOrderFinNormedModule.axioms_ R C) := 
  PseudoMetricNormedZmod.Class (VOrderFinNormedModule.normedtype_NormedZmod_PseudoMetric_eq_mixin c).
#[reversible] Coercion extnum_VOrderFinNormedModule_class__to__normedtype_PseudoMetricNormedZmod_class : 
  VOrderFinNormedModule.axioms_ >-> PseudoMetricNormedZmod.axioms_.

Definition extnum_VOrderFinNormedModule_class__to__GRing_Lmodule_class
  (R : numFieldType) (C : Type) (c : VOrderFinNormedModule.axioms_ R C) := 
  GRing.Lmodule.Class (VOrderFinNormedModule.GRing_Zmodule_isLmodule_mixin c).
#[reversible] Coercion extnum_VOrderFinNormedModule_class__to__GRing_Lmodule_class : 
  VOrderFinNormedModule.axioms_ >-> GRing.Lmodule.axioms_.

Definition extnum_VOrderFinNormedModule_class__to__normedtype_NormedModule_class
  (R : numFieldType) (C : Type) (c : VOrderFinNormedModule.axioms_ R C) := 
  NormedModule.Class 
  (VOrderFinNormedModule.normedtype_PseudoMetricNormedZmod_Lmodule_isNormedModule_mixin c).
#[reversible] Coercion extnum_VOrderFinNormedModule_class__to__normedtype_NormedModule_class : 
  VOrderFinNormedModule.axioms_ >-> NormedModule.axioms_.

Definition extnum_VOrderFinNormedModule_class__to__vector_Vector_class
  (R : numFieldType) (C : Type) (c : VOrderFinNormedModule.axioms_ R C) := 
  vector.Vector.Class (VOrderFinNormedModule.vector_Lmodule_hasFinDim_mixin c).
#[reversible] Coercion extnum_VOrderFinNormedModule_class__to__vector_Vector_class : 
  VOrderFinNormedModule.axioms_ >-> vector.Vector.axioms_.

Definition extnum_VOrderFinNormedModule_class__to__extnum_FinNormedModule_class
  (R : numFieldType) (C : Type) (c : VOrderFinNormedModule.axioms_ R C) := 
  FinNormedModule.Class
  (VOrderFinNormedModule.vector_Lmodule_hasFinDim_mixin c)
  (VOrderFinNormedModule.normedtype_PseudoMetricNormedZmod_Lmodule_isNormedModule_mixin c).
#[reversible] Coercion extnum_VOrderFinNormedModule_class__to__extnum_FinNormedModule_class : 
  VOrderFinNormedModule.axioms_ >-> FinNormedModule.axioms_.

Definition extnum_VOrderFinNormedModule_class__to__mxpred_POrderedLmodule_class
  (R : numFieldType) (C : Type) (c : VOrderFinNormedModule.axioms_ R C) := 
  POrderedLmodule.Class (VOrderFinNormedModule.GRing_Zmodule_isLmodule_mixin c)
  (VOrderFinNormedModule.Order_isPOrder_mixin c).
#[reversible] Coercion extnum_VOrderFinNormedModule_class__to__mxpred_POrderedLmodule_class : 
  VOrderFinNormedModule.axioms_ >-> POrderedLmodule.axioms_.

Definition extnum_VOrderFinNormedModule_class__to__mxpred_VOrder_class
  (R : numFieldType) (C : Type) (c : VOrderFinNormedModule.axioms_ R C) := 
  VOrder.Class (VOrderFinNormedModule.mxpred_POrderedLmodule_isVOrder_mixin c).
#[reversible] Coercion extnum_VOrderFinNormedModule_class__to__mxpred_VOrder_class : 
  VOrderFinNormedModule.axioms_ >-> VOrder.axioms_.

(* type.axioms_ >-> mixin.axioms_ reversible Coercion *)
#[reversible] Coercion VOrderFinNormedModule.classical_sets_isPointed_mixin : 
  VOrderFinNormedModule.axioms_ >-> isPointed.axioms_.
#[reversible] Coercion VOrderFinNormedModule.topology_selfFiltered_mixin : 
  VOrderFinNormedModule.axioms_ >-> selfFiltered.axioms_.
#[reversible] Coercion VOrderFinNormedModule.topology_isFiltered_mixin : 
  VOrderFinNormedModule.axioms_ >-> isFiltered.axioms_.
#[reversible] Coercion VOrderFinNormedModule.GRing_isNmodule_mixin : 
  VOrderFinNormedModule.axioms_ >-> GRing.isNmodule.axioms_.
#[reversible] Coercion VOrderFinNormedModule.choice_hasChoice_mixin : 
  VOrderFinNormedModule.axioms_ >-> hasChoice.axioms_.
#[reversible] Coercion VOrderFinNormedModule.eqtype_hasDecEq_mixin : 
  VOrderFinNormedModule.axioms_ >-> Equality.mixin_of.
#[reversible] Coercion VOrderFinNormedModule.topology_Nbhs_isUniform_mixin_mixin : 
  VOrderFinNormedModule.axioms_ >-> Nbhs_isUniform_mixin.axioms_.
#[reversible] Coercion VOrderFinNormedModule.topology_Nbhs_isTopological_mixin : 
  VOrderFinNormedModule.axioms_ >-> Nbhs_isTopological.axioms_.
#[reversible] Coercion VOrderFinNormedModule.topology_Uniform_isPseudoMetric_mixin : 
  VOrderFinNormedModule.axioms_ >-> Uniform_isPseudoMetric.axioms_.
#[reversible] Coercion VOrderFinNormedModule.GRing_Nmodule_isZmodule_mixin : 
  VOrderFinNormedModule.axioms_ >-> GRing.Nmodule_isZmodule.axioms_.
#[reversible] Coercion VOrderFinNormedModule.Num_Zmodule_isNormed_mixin : 
  VOrderFinNormedModule.axioms_ >-> Num.Zmodule_isNormed.axioms_.
#[reversible] Coercion VOrderFinNormedModule.normedtype_NormedZmod_PseudoMetric_eq_mixin : 
  VOrderFinNormedModule.axioms_ >-> NormedZmod_PseudoMetric_eq.axioms_.
#[reversible] Coercion VOrderFinNormedModule.GRing_Zmodule_isLmodule_mixin : 
  VOrderFinNormedModule.axioms_ >-> GRing.Zmodule_isLmodule.axioms_.
#[reversible] Coercion VOrderFinNormedModule.normedtype_PseudoMetricNormedZmod_Lmodule_isNormedModule_mixin : 
  VOrderFinNormedModule.axioms_ >-> PseudoMetricNormedZmod_Lmodule_isNormedModule.axioms_.
#[reversible] Coercion VOrderFinNormedModule.vector_Lmodule_hasFinDim_mixin : 
  VOrderFinNormedModule.axioms_ >-> Vector.mixin_of.
#[reversible] Coercion VOrderFinNormedModule.Order_isPOrder_mixin : 
  VOrderFinNormedModule.axioms_ >-> isPOrder.axioms_.
#[reversible] Coercion VOrderFinNormedModule.mxpred_POrderedLmodule_isVOrder_mixin : 
  VOrderFinNormedModule.axioms_ >-> POrderedLmodule_isVOrder.axioms_.
#[reversible] Coercion VOrderFinNormedModule.extnum_FinNormedModule_isVOrderFinNormedModule_mixin : 
  VOrderFinNormedModule.axioms_ >-> FinNormedModule_isVOrderFinNormedModule.axioms_.

(* type.type >-> type.type reversible Coercion & Canonical *)
Definition extnum_VOrderFinNormedModule__to__eqtype_Equality
  (R : numFieldType) (C : vorderFinNormedModType R) :=
  Equality.Pack (VOrderFinNormedModule.class C).
#[reversible] Coercion extnum_VOrderFinNormedModule__to__eqtype_Equality : 
  VOrderFinNormedModule.type >-> Equality.type.
Canonical extnum_VOrderFinNormedModule__to__eqtype_Equality.

Definition extnum_VOrderFinNormedModule__to__choice_Choice 
  (R : numFieldType) (C : vorderFinNormedModType R) := 
  Choice.Pack (VOrderFinNormedModule.class C).
#[reversible] Coercion extnum_VOrderFinNormedModule__to__choice_Choice: 
  VOrderFinNormedModule.type >-> Choice.type.
Canonical extnum_VOrderFinNormedModule__to__choice_Choice.

Definition extnum_VOrderFinNormedModule__to__GRing_Nmodule 
  (R : numFieldType) (C : vorderFinNormedModType R) := 
  GRing.Nmodule.Pack (VOrderFinNormedModule.class C).
#[reversible] Coercion extnum_VOrderFinNormedModule__to__GRing_Nmodule: 
  VOrderFinNormedModule.type >-> GRing.Nmodule.type.
Canonical extnum_VOrderFinNormedModule__to__GRing_Nmodule.

Definition extnum_VOrderFinNormedModule__to__GRing_Zmodule 
  (R : numFieldType) (C : vorderFinNormedModType R) := 
  GRing.Zmodule.Pack (VOrderFinNormedModule.class C).
#[reversible] Coercion extnum_VOrderFinNormedModule__to__GRing_Zmodule: 
  VOrderFinNormedModule.type >-> GRing.Zmodule.type.
Canonical extnum_VOrderFinNormedModule__to__GRing_Zmodule.

Definition extnum_VOrderFinNormedModule__to__Num_NormedZmodule 
  (R : numFieldType) (C : vorderFinNormedModType R) := 
  Num.NormedZmodule.Pack (VOrderFinNormedModule.class C).
#[reversible] Coercion extnum_VOrderFinNormedModule__to__Num_NormedZmodule: 
  VOrderFinNormedModule.type >-> Num.NormedZmodule.type.
Canonical extnum_VOrderFinNormedModule__to__Num_NormedZmodule.

Definition extnum_VOrderFinNormedModule__to__Order_POrder
  (R : numFieldType) (C : vorderFinNormedModType R) := 
  POrder.Pack (VOrderFinNormedModule.class C).
#[reversible] Coercion extnum_VOrderFinNormedModule__to__Order_POrder : 
  VOrderFinNormedModule.type >-> POrder.type.
Canonical extnum_VOrderFinNormedModule__to__Order_POrder.

Definition extnum_VOrderFinNormedModule__to__Num_POrderedZmodule 
  (R : numFieldType) (C : vorderFinNormedModType R) := 
  Num.POrderedZmodule.Pack (VOrderFinNormedModule.class C).
#[reversible] Coercion extnum_VOrderFinNormedModule__to__Num_POrderedZmodule : 
  VOrderFinNormedModule.type >-> Num.POrderedZmodule.type.
Canonical extnum_VOrderFinNormedModule__to__Num_POrderedZmodule.

Definition extnum_VOrderFinNormedModule__to__classical_sets_Pointed
  (R : numFieldType) (C : vorderFinNormedModType R) := 
  classical_sets.Pointed.Pack (VOrderFinNormedModule.class C).
#[reversible] Coercion extnum_VOrderFinNormedModule__to__classical_sets_Pointed : 
  VOrderFinNormedModule.type >-> Pointed.type.
Canonical extnum_VOrderFinNormedModule__to__classical_sets_Pointed.

Definition extnum_VOrderFinNormedModule__to__topology_Filtered
  (R : numFieldType) (C : vorderFinNormedModType R) := 
  Filtered.Pack (VOrderFinNormedModule.class C).
#[reversible] Coercion extnum_VOrderFinNormedModule__to__topology_Filtered : 
  VOrderFinNormedModule.type >-> Filtered.type.
Canonical extnum_VOrderFinNormedModule__to__topology_Filtered.

Definition extnum_VOrderFinNormedModule__to__topology_Nbhs
  (R : numFieldType) (C : vorderFinNormedModType R) := 
  Nbhs.Pack (VOrderFinNormedModule.class C).
#[reversible] Coercion extnum_VOrderFinNormedModule__to__topology_Nbhs : 
  VOrderFinNormedModule.type >-> Nbhs.type.
Canonical extnum_VOrderFinNormedModule__to__topology_Nbhs.

Definition extnum_VOrderFinNormedModule__to__topology_Topological
  (R : numFieldType) (C : vorderFinNormedModType R) := 
  Topological.Pack (VOrderFinNormedModule.class C).
#[reversible] Coercion extnum_VOrderFinNormedModule__to__topology_Topological : 
  VOrderFinNormedModule.type >-> Topological.type.
Canonical extnum_VOrderFinNormedModule__to__topology_Topological.

Definition extnum_VOrderFinNormedModule__to__topology_Uniform
  (R : numFieldType) (C : vorderFinNormedModType R) := 
  Uniform.Pack (VOrderFinNormedModule.class C).
#[reversible] Coercion extnum_VOrderFinNormedModule__to__topology_Uniform : 
  VOrderFinNormedModule.type >-> Uniform.type.
Canonical extnum_VOrderFinNormedModule__to__topology_Uniform.

Definition extnum_VOrderFinNormedModule__to__topology_PseudoMetric
  (R : numFieldType) (C : vorderFinNormedModType R) := 
  PseudoMetric.Pack (VOrderFinNormedModule.class C).
#[reversible] Coercion extnum_VOrderFinNormedModule__to__topology_PseudoMetric : 
  VOrderFinNormedModule.type >-> PseudoMetric.type.
Canonical extnum_VOrderFinNormedModule__to__topology_PseudoMetric.

Definition extnum_VOrderFinNormedModule__to__normedtype_PseudoMetricNormedZmod
  (R : numFieldType) (C : vorderFinNormedModType R) := 
  PseudoMetricNormedZmod.Pack (VOrderFinNormedModule.class C).
#[reversible] Coercion extnum_VOrderFinNormedModule__to__normedtype_PseudoMetricNormedZmod : 
  VOrderFinNormedModule.type >-> PseudoMetricNormedZmod.type.
Canonical extnum_VOrderFinNormedModule__to__normedtype_PseudoMetricNormedZmod.

Definition extnum_VOrderFinNormedModule__to__GRing_Lmodule
  (R : numFieldType) (C : vorderFinNormedModType R) := 
  GRing.Lmodule.Pack (VOrderFinNormedModule.class C).
#[reversible] Coercion extnum_VOrderFinNormedModule__to__GRing_Lmodule : 
  VOrderFinNormedModule.type >-> GRing.Lmodule.type.
Canonical extnum_VOrderFinNormedModule__to__GRing_Lmodule.

Definition extnum_VOrderFinNormedModule__to__normedtype_NormedModule
  (R : numFieldType) (C : vorderFinNormedModType R) := 
  NormedModule.Pack (VOrderFinNormedModule.class C).
#[reversible] Coercion extnum_VOrderFinNormedModule__to__normedtype_NormedModule : 
  VOrderFinNormedModule.type >-> NormedModule.type.
Canonical extnum_VOrderFinNormedModule__to__normedtype_NormedModule.

Definition extnum_VOrderFinNormedModule__to__vector_Vector
  (R : numFieldType) (C : vorderFinNormedModType R) := 
  vector.Vector.Pack (VOrderFinNormedModule.class C).
#[reversible] Coercion extnum_VOrderFinNormedModule__to__vector_Vector : 
  VOrderFinNormedModule.type >-> vector.Vector.type.
Canonical extnum_VOrderFinNormedModule__to__vector_Vector.

Definition extnum_VOrderFinNormedModule__to__extnum_FinNormedModule
  (R : numFieldType) (C : vorderFinNormedModType R) := 
  FinNormedModule.Pack (VOrderFinNormedModule.class C).
#[reversible] Coercion extnum_VOrderFinNormedModule__to__extnum_FinNormedModule : 
  VOrderFinNormedModule.type >-> FinNormedModule.type.
Canonical extnum_VOrderFinNormedModule__to__extnum_FinNormedModule.

Definition extnum_VOrderFinNormedModule__to__mxpred_POrderedLmodule
  (R : numFieldType) (C : vorderFinNormedModType R) := 
  POrderedLmodule.Pack (VOrderFinNormedModule.class C).
#[reversible] Coercion extnum_VOrderFinNormedModule__to__mxpred_POrderedLmodule : 
  VOrderFinNormedModule.type >-> POrderedLmodule.type.
Canonical extnum_VOrderFinNormedModule__to__mxpred_POrderedLmodule.

Definition extnum_VOrderFinNormedModule__to__mxpred_VOrder
  (R : numFieldType) (C : vorderFinNormedModType R) := 
  VOrder.Pack (VOrderFinNormedModule.class C).
#[reversible] Coercion extnum_VOrderFinNormedModule__to__mxpred_VOrder : 
  VOrderFinNormedModule.type >-> VOrder.type.
Canonical extnum_VOrderFinNormedModule__to__mxpred_VOrder.

(* usage: after build the mixin, manually add the canonical structure of type *)
(* HB.instance Definition XXX_vorderFinNormedModMixin := FinNormedModule_isVOrderFinNormedModule.Build
Canonical XXX__canonical__extnum_VOrderFinNormedModule := 
  VOrderFinNormedModule.Pack (VOrderFinNormedModule.Class XXX_vorderFinNormedModMixin). *)

Module VOrderFinNormedModuleExports.
#[deprecated(since="mathcomp 2.0.0", note="Use VOrderFinNormedModule.clone instead.")]
Notation "[ 'vorderFinNormedModType' C 'of' T 'for' cT ]" := (VOrderFinNormedModule.clone C T%type cT)
  (at level 0, format "[ 'vorderFinNormedModType'  C  'of'  T  'for'  cT ]") : form_scope.
#[deprecated(since="mathcomp 2.0.0", note="Use VOrderFinNormedModule.clone instead.")]
Notation "[ 'vorderFinNormedModType' C 'of' T ]" := (VOrderFinNormedModule.clone C T%type _)
  (at level 0, format "[ 'vorderFinNormedModType'  C  'of'  T ]") : form_scope.
End VOrderFinNormedModuleExports.
HB.export VOrderFinNormedModuleExports.

Section FinNormedModTypeComplete.
Context {R : realType} {C : extNumType R} {V : finNormedModType C}.
Import VectorInternalTheory Num.Def Num.Theory numFieldNormedType.Exports.

Lemma bounded_normr_mxnorm m n (f: V -> 'M[C]_(m,n)) (lf: linear f) (bf: bijective f) :
  (exists c, c > 0 /\ forall x : V, `|x| <= c * mx_norm (f x))
  /\ (exists c, c > 0 /\ forall x : V, mx_norm (f x) <= c * `|x|).
Proof.
move: bf=>[g fK gK]; move: (can2_linearP lf fK gK)=>lg.
pose mn x := `|g x|.
have meq0 : forall x, mn x = 0 -> x = 0.
  by move=>x/normr0_eq0; rewrite -{2}(gK x)/==>->; rewrite (linearlfE lf) linear0.
have mtrg : forall x y, mn (x + y) <= mn x + mn y.
  by move=>x y; rewrite /mn (linearlfE lg) linearD ler_normD.
have mZ : forall (a: C) (x : 'M_(m,n)), mn (a *: x) = `|a| * mn x.
  by move=>a x; rewrite /mn (linearlfE lg) linearZ normrZ.
pose mvn := VNorm.Pack (VNorm.Class (isVNorm.Build _ 'M[C]_(m,n) mn mtrg meq0 mZ)).
have x2m : forall x, `|x| = mn (f x) by move=>x; rewrite /mn fK.
split. move: (mnorm_bounded mvn (@mx_norm_vnorm _ _ _))=>[c /= cgt0 Pml].
2: move: (mnorm_bounded (@mx_norm_vnorm _ _ _) mvn)=>[c /= cgt0 Pml].
all: exists c; split=>// x; by rewrite x2m.
Qed.

Lemma bounded_mxnorm_normr (m n: nat) (g: 'M[C]_(m,n) -> V) (lg: linear g) (bg: bijective g) :
  (exists c, c > 0 /\ forall x : 'M[C]_(m,n), mx_norm x <= c * `|g x|)
  /\ (exists c, c > 0 /\ forall x : 'M[C]_(m,n), `|g x| <= c * mx_norm x).
Proof.
move: bg=>[f gK fK]. move: (bounded_normr_mxnorm (can2_linearP lg gK fK) 
  (can2_bij gK fK))=>[[c1 [c1gt0 Pc1]] [c2 [c2gt0 Pc2]]].
split. exists c2; split=>// x; by rewrite -{1}(gK x).
exists c1; split=>// x; by rewrite -{2}(gK x).
Qed.

Lemma bijective_to_mx_continuous (m n: nat) (f: V -> 'M[C]_(m,n)) 
  (lf: linear f) (bf: bijective f) : continuous f.
Proof.
case: m f lf bf=>[f _ _|]; last case: n=>[m f _ _|m n f lf bf].
1,2: by rewrite mx_dim0=>x; apply: cst_continuous.
rewrite (linearlfE lf) -linear_bounded_continuous -bounded_funP=>r/=.
move: (bounded_normr_mxnorm lf bf)=>[_ [c2 [c2gt0 Pc2]]].
exists (c2 * r)=>x. rewrite -(ler_pM2l c2gt0) {2}/normr/=.
apply (le_trans (Pc2 _)).
Qed.

Lemma bijective_of_mx_continuous (m n: nat) (g: 'M[C]_(m,n) -> V) 
  (lg: linear g) (bg: bijective g) : continuous g.
Proof.
case: m g lg bg=>[g _ _|]; last case: n=>[m g _ _|m n g lg bg].
1,2: by apply: cst_continuous_eq; exists (g 0); apply/funext=>i; rewrite mx_dim0.
rewrite (linearlfE lg) -linear_bounded_continuous -bounded_funP=>r/=.
move: (bounded_mxnorm_normr lg bg)=>[_ [c2 [c2gt0 Pc2]]].
exists (c2 * r)=>x. rewrite -(ler_pM2l c2gt0) {1}/normr/=.
apply (le_trans (Pc2 _)).
Qed.

Lemma bijective_to_mx_cvgnE (m n: nat) (f: V -> 'M[C]_(m,n)) (u : nat -> V) 
  (a : V) (lf: linear f) (bf: bijective f) :
  u @ \oo --> a = ((f \o u)%FUN @ \oo --> f a).
Proof.
rewrite propeqE; split; last move: {+}bf=>[g fK gK].
by apply: continuous_cvg; apply/(bijective_to_mx_continuous lf bf).
have P: u = (g \o (f \o u))%FUN by apply/funext=>i/=; rewrite fK.
have P1: a = g (f a) by rewrite fK. 
rewrite [in X in _ -> X]P [in X in _ -> X]P1; apply: continuous_cvg. 
apply (bijective_of_mx_continuous (can2_linearP lf fK gK) (can2_bij fK gK)).
Qed.

Lemma bijective_of_mx_cvgnE (m n: nat) (f: 'M[C]_(m,n) -> V) 
  (u : nat -> 'M[C]_(m,n)) (a : 'M[C]_(m,n)) (lf: linear f) (bf: bijective f) :
  u @ \oo --> a = ((f \o u)%FUN @ \oo --> f a).
Proof.
rewrite propeqE; split; last move: {+}bf=>[g fK gK].
by apply: continuous_cvg; apply/(bijective_of_mx_continuous lf bf).
have P: u = (g \o (f \o u))%FUN by apply/funext=>i/=; rewrite fK.
have P1: a = g (f a) by rewrite fK. 
rewrite [in X in _ -> X]P [in X in _ -> X]P1; apply: continuous_cvg. 
apply (bijective_to_mx_continuous (can2_linearP lf fK gK) (can2_bij fK gK)).
Qed.

Lemma bijective_to_mx_is_cvgnE (m n: nat) (f: V -> 'M[C]_(m,n)) (u : nat -> V)
  (lf: linear f) (bf: bijective f) : cvgn u = cvgn (f \o u)%FUN.
Proof.
rewrite propeqE; split; move=>/cvg_ex[a Pa]; apply/cvg_ex.
exists (f a); by rewrite -bijective_to_mx_cvgnE.
move: {+}bf=>[g fK gK]; exists (g a); move: Pa.
have P1: a = f (g a) by [].
by rewrite [in X in X -> _]P1 -bijective_to_mx_cvgnE.
Qed.

Lemma bijective_of_mx_is_cvgnE (m n: nat) (f: 'M[C]_(m,n) -> V) 
  (u : nat -> 'M[C]_(m,n)) (lf: linear f) (bf: bijective f) :
  cvgn u = cvgn (f \o u)%FUN.
Proof.
rewrite propeqE; split; move/cvg_ex=>[a Pa]; apply/cvg_ex.
exists (f a); by rewrite -bijective_of_mx_cvgnE.
move: {+}bf=>[g fK gK]; exists (g a); move: Pa.
have P1: a = f (g a) by []. 
by rewrite [in X in X -> _]P1 -bijective_of_mx_cvgnE.
Qed.

Lemma bijective_to_mx_limnE (m n: nat) (f: V -> 'M[C]_(m,n)) (u : nat -> V)
  (lf: linear f) (bf: bijective f) :
  cvgn u -> limn (f \o u)%FUN = f (limn u).
Proof.
move=>?; apply: cvg_lim; first by apply: mxhausdorff.
by rewrite -bijective_to_mx_cvgnE.
Qed.

Lemma bijective_of_mx_limnE (m n: nat) (f: 'M[C]_(m,n) -> V) 
  (u : nat -> 'M[C]_(m,n)) (lf: linear f) (bf: bijective f) :
  cvgn u -> limn (f \o u)%FUN = f (limn u).
Proof.
move=> ?; apply: cvg_lim; first by apply: norm_hausdorff.
by rewrite -bijective_of_mx_cvgnE.
Qed.

Local Notation MV := 'rV[C]_(dim V).

Lemma v2r_continuous : continuous (@v2r _ V).
Proof. apply: (bijective_to_mx_continuous _ v2r_bij); exact: linearP. Qed.

Lemma r2v_continuous : continuous (@r2v _ V).
Proof. apply: (bijective_of_mx_continuous _ r2v_bij); exact: linearP. Qed.

Lemma v2r_cvgnE (u : nat -> V) (a : V): u @ \oo --> a = ((v2r \o u)%FUN @ \oo --> v2r a).
Proof. apply: (bijective_to_mx_cvgnE _ _ _ v2r_bij); exact: linearP. Qed.

Lemma r2v_cvgnE (u : nat -> MV) (a : MV) : u @ \oo --> a = ((r2v \o u)%FUN @ \oo --> r2v a).
Proof. apply: (bijective_of_mx_cvgnE _ _ _ r2v_bij); exact: linearP. Qed.

Lemma v2r_is_cvgnE (u : nat -> V) : cvgn u = cvgn (v2r \o u)%FUN.
Proof. apply: (bijective_to_mx_is_cvgnE _ _ v2r_bij); exact: linearP. Qed.

Lemma r2v_is_cvgnE (u : nat -> MV) : cvgn u = cvgn (r2v \o u)%FUN.
Proof. apply: (bijective_of_mx_is_cvgnE _ _ r2v_bij). exact: linearP. Qed.

Lemma v2r_limnE (u : nat -> V) : cvgn u -> limn (v2r \o u)%FUN = v2r (limn u).
Proof. apply: (bijective_to_mx_limnE _ v2r_bij); exact: linearP. Qed.

Lemma r2v_limnE (u : nat -> MV) : cvgn u -> limn (r2v \o u)%FUN = r2v (limn u).
Proof. apply: (bijective_of_mx_limnE _ r2v_bij); exact: linearP. Qed.

(* Definition finNormedMod_vnorm := VNorm.Pack (VNorm.Class (
  isVNorm.Build C V (@normr C V) (@ler_normD C V) (@normr0_eq0 C V) (@normrZ C V))). *)

(* vnorm V transform to vnorm of matrix *)
Program Definition v2r_vnorm_mixin (f : vnorm V) := @isVNorm.Build C 'rV[C]_(dim V) (fun x=>f (r2v x)) _ _ _.
Next Obligation. 
by move=>f x y /=; rewrite linearD/= lev_normD.
Qed.
Next Obligation.
by move=>f x /= /normv0_eq0; rewrite -{2}(r2vK x)=>->; rewrite linear0.
Qed.
Next Obligation.
by move=>f a x/=; rewrite !linearZ/= normvZ.
Qed.
Definition v2r_vnorm (f : vnorm V) := VNorm.Pack (VNorm.Class (v2r_vnorm_mixin f)).

Program Definition r2v_vnorm_mixin (f : vnorm _) := @isVNorm.Build C V (fun x=>f (v2r x)) _ _ _.
Next Obligation.
by move=>f x y /=; rewrite linearD/= lev_normD.
Qed.
Next Obligation.
by move=>f x /= /normv0_eq0; rewrite -{2}(v2rK x)=>->; rewrite linear0.
Qed.
Next Obligation.
by move=>f a x/=; rewrite !linearZ/= normvZ.
Qed.
Definition r2v_vnorm (f : vnorm _) := VNorm.Pack (VNorm.Class (r2v_vnorm_mixin f)).

Lemma r2vK_vnorm (f : vnorm _) x : v2r_vnorm (r2v_vnorm f) x = f x.
Proof. by rewrite /= r2vK. Qed.
Lemma v2rK_vnorm (f : vnorm V) x : r2v_vnorm (v2r_vnorm f) x = f x.
Proof. by rewrite /= v2rK. Qed.
Lemma r2v_vnormE (f : vnorm _) x : f x = r2v_vnorm f (r2v x).
Proof. by rewrite /= r2vK. Qed.
Lemma v2r_vnormE (f : vnorm V) x : f x = v2r_vnorm f (v2r x).
Proof. by rewrite /= v2rK. Qed.

Lemma compact_norm_le (e : C) : compact [set x : V | `|x| <= e].
Proof.
rewrite (_ : mkset _ = r2v @` [set x | v2r_vnorm normr x <= e]).
apply: continuous_compact; last by apply: compact_mnorm_le.
apply: continuous_subspaceT=>x ?; apply: r2v_continuous.
rewrite predeqE=>/=x; split=>[Px|[y Py1 <-//]].
by exists (v2r x); rewrite/= v2rK.
Qed.

Lemma V_complete (F : set_system V) :
  ProperFilter F -> cauchy F -> cvg F.
Proof. by apply: bounded_compact_complete; apply: compact_norm_le. Qed.

End FinNormedModTypeComplete.

Arguments bijective_to_mx_cvgnE [R C V m n f u a].
Arguments bijective_of_mx_cvgnE [R C V m n f u a].
Arguments bijective_to_mx_is_cvgnE [R C V m n f u].
Arguments bijective_of_mx_is_cvgnE [R C V m n f u].
Arguments bijective_to_mx_limnE [R C V m n f u].
Arguments bijective_of_mx_limnE [R C V m n f u].

HB.instance Definition _ (R : realType) (C : extNumType R) (V : finNormedModType C) :=
  Uniform_isComplete.Build V (@V_complete R C V).
HB.instance Definition _ (R : realType) (C : extNumType R) (V : vorderFinNormedModType C) :=
  Uniform_isComplete.Build V (@V_complete R C V).

Section FinNormedModTheory.
Context {R : realType} {C : extNumType R} {V : finNormedModType C}.
Import Num.Def Num.Theory VectorInternalTheory.
Implicit Type (f g: nat -> V) (n: nat) (s a b : V).

Lemma Vhausdorff : hausdorff_space V.
Proof. exact: norm_hausdorff. Qed.

Lemma vcvgn_limnE f a : f @ \oo --> a <-> limn f = a /\ cvgn f.
Proof. exact: (cvgn_limnE f a Vhausdorff). Qed.

Lemma vcvgn_map f a (U : completeType) (h : V -> U) :
  continuous h -> f @ \oo --> a -> (h \o f) @ \oo --> h a.
Proof. 
move=>ch cvgf; apply: (@cvg_fmap _ _ (nbhs (f @ \oo)) a h).
by apply ch. by apply cvgf.
Qed.

Lemma vcvgn_mapV (U : completeType) (h : U -> V) (h' : nat -> U) (a : U) :
  continuous h -> h' @ \oo --> a -> (h \o h') @ \oo --> h a.
Proof. 
move=>ch cvgf; apply: (@cvg_fmap _ _ (nbhs (h' @ \oo)) a h).
by apply ch. by apply cvgf.
Qed.

Lemma is_vcvgn_map f (U : completeType) (h : V -> U) :
  continuous h -> cvgn f -> cvgn (h \o f).
Proof.
move=>P1 /cvg_ex=>[/= [a Pa]]. apply/cvg_ex.
exists (h a). by move: (vcvgn_map P1 Pa).
Qed.

Lemma is_vcvgn_mapV (U : completeType) (h : U -> V) (h' : nat -> U) :
  continuous h -> cvgn h' -> cvgn (h \o h').
Proof.
move=>P1 /cvg_ex=>[/= [a Pa]]. apply/cvg_ex.
exists (h a). by move: (vcvgn_mapV P1 Pa).
Qed.

Lemma vlimn_map f (U : completeType) (h : V -> U) :
  hausdorff_space U -> continuous h -> cvgn f -> limn (h \o f) = h (limn f).
Proof. by move=>hV ch; move/(vcvgn_map ch)/cvg_lim=>/(_ hV). Qed.

Lemma vlimn_mapV (U : completeType) (h : U -> V) (h' : nat -> U) :
  continuous h -> cvgn h' -> limn (h \o h') = h (limn h').
Proof. by move=>ch; move/(vcvgn_mapV ch)/cvg_lim=>/(_ Vhausdorff). Qed.

Lemma vcvgn_limnP f a :
  f @ \oo --> a <-> forall e, 0 < e -> exists N, forall n,  (N <= n)%N -> `|f n - a| < e.
Proof. exact: cvgn_limnP. Qed.

Lemma vcvgn_subseqP f a : 
  f @ \oo --> a <-> (forall (h: nat -> nat), (forall n, (h n.+1 > h n)%N) -> (f \o h) @ \oo --> a).
Proof. exact: cvgn_subseqP. Qed.

Lemma vcvgn_subseqPN f a :
  ~ (f @ \oo --> a) <-> exists e (h: nat -> nat), 
    (forall n, (h n.+1 > h n)%N) /\ 0 < e /\ (forall n, `|(f \o h) n - a| >= e).
Proof. exact: cvgn_subseqPN. Qed.

(* equivalence of vnorm of V *)
(* linear continuous *)
Lemma normv_bounded (f g : vnorm V):
  exists2 c : C, 0 < c & forall x, f x <= c * g x.
Proof.
move: (mnorm_bounded (v2r_vnorm f) (v2r_vnorm g))=>[c cgt0 Pc].
exists c=>// x; by rewrite !v2r_vnormE.
Qed.

Lemma normv_ubounded (f : vnorm V) : 
  exists2 c, 0 < c & forall x, f x <= c * `| x |.
Proof. exact: normv_bounded. Qed.

Lemma normv_lbounded (f : vnorm V) : 
  exists2 c, 0 < c & forall x, c * `| x | <= f x.
Proof.
move: (normv_bounded normr f)=>[c cgt0 Pc].
by exists (c^-1)=>[|x]; rewrite ?ler_pdivrMl// ?Pc// invr_gt0.
Qed.

Lemma cauchy_seqv_defaultE f :
  cauchy_seqv normr f <-> cauchy_seq f.
Proof. by []. Qed.

Lemma cauchy_seqv_eq (nv1 nv2 : vnorm V) f :
  cauchy_seqv nv1 f <-> cauchy_seqv nv2 f.
split.
move: (normv_bounded nv2 nv1). 2: move: (normv_bounded nv1 nv2).
all: move=> [c Pc le_mn] P e Pe.
all: have Pec: 0 < (e / c) by apply divr_gt0.
all: move: (P (e/c) Pec )=>[N PN]; exists N=>s t Ps Pt.
all: apply: (le_lt_trans (le_mn (f s - f t))).
all: by rewrite -ltr_pdivlMl// mulrC PN.
Qed.

Lemma cauchy_seqv_cvgn (nv : vnorm V) f :
  cauchy_seqv nv f <-> cvgn f.
Proof.
rewrite (@cauchy_seqv_eq _ normr).
exact: cauchy_seqP.
Qed.

Lemma normv_continuous (nv : vnorm V) : continuous nv.
Proof.
suff <-: (v2r_vnorm nv) \o v2r = nv.
apply: continuous_comp_simp. apply: v2r_continuous.
apply: continuous_mnorm.
by apply/funext=>x /=; rewrite v2rK.
Qed.

Context {T : Type} (F : set_system T) {FF : ProperFilter F}.
Variable (nv : vnorm V).
Implicit Type (h : T -> V) (v : V).

Lemma cvg_normv h v : h @ F --> v -> nv (h x) @[x --> F] --> nv v.
Proof. by apply: continuous_cvg; apply: normv_continuous. Qed.

Lemma is_cvg_normv h : cvg (h @ F) -> cvg ((nv \o h : T -> C) @ F).
Proof. by have := cvgP _ (cvg_normv _); apply. Qed.

Lemma lim_normv h : cvg (h @ F) -> lim ((fun x => nv (h x)) @ F) = nv (lim (h @ F)).
Proof. by move=> ?; apply: cvg_lim => //; apply: cvg_normv. Qed.

End FinNormedModTheory.

Section LinearContinuous.
Context {R : realType} {C : extNumType R}.
Variable (T : Type) (F : set_system T).
Implicit Type (FF : Filter F) (PF: ProperFilter F).

Import VectorInternalTheory.
Implicit Type (U V W: finNormedModType C).

Lemma linear_continuous {U V} (f : {linear U -> V}) :
  continuous f.
Proof.
pose g x := v2r (f (r2v x)); suff <-: r2v \o g \o v2r = f.
apply: continuous_comp_simp; first by apply: v2r_continuous.
apply: continuous_comp_simp; last by apply: r2v_continuous.
by apply/mxlinear_continuous=>a x y; rewrite /g !linearP.
by apply/funext=>x; rewrite /g/= !v2rK.
Qed.

Lemma linear_continuousP {U V} (f : U -> V) :
  linear f -> continuous f.
Proof. move=>lf; rewrite (linearlfE lf); exact: linear_continuous. Qed.

Lemma linear_cvg {FF} {U V} (f : {linear U -> V}) (u : T -> U) (a : U) :
  u @ F --> a -> f \o u @ F --> f a.
Proof. move=>cu. apply: continuous_cvg=>//. apply: linear_continuous. Qed.

Lemma linear_cvgP {FF} {U V} (f : U -> V) (u : T -> U) (a : U) :
  linear f -> u @ F --> a -> f \o u @ F --> f a.
Proof. move=>lf; rewrite (linearlfE lf); exact: linear_cvg. Qed.

Lemma linear_is_cvg {FF} {U V} (f : {linear U -> V}) (u : T -> U) :
  cvg (u @ F) -> cvg (f \o u @ F).
Proof. move/cvg_ex=>[a Pa]; apply/cvg_ex; exists (f a); by apply: linear_cvg. Qed.

Lemma linear_is_cvgP {FF} {U V} (f : U -> V) (u : T -> U) :
  linear f -> cvg (u @ F) -> cvg (f \o u @ F).
Proof. move=>lf; rewrite (linearlfE lf); exact: linear_is_cvg. Qed.

Lemma linear_lim {PF} {U V} (f : {linear U -> V}) (u : T -> U) :
  cvg (u @ F) -> lim (f \o u @ F) = f (lim (u @ F)).
Proof. by move=>cu; apply: cvg_lim; [apply: Vhausdorff | apply: linear_cvg]. Qed.

Lemma linear_limP {PF} {U V} (f : U -> V) (u : T -> U) :
  linear f -> cvg (u @ F) -> lim (f \o u @ F) = f (lim (u @ F)).
Proof. move=>lf; rewrite (linearlfE lf); exact: linear_lim. Qed.

Section BilinearRContinuous.
Variable (FF : Filter F) (PF: ProperFilter F) (U V W: finNormedModType C).
Variable (f : {bilinear U -> V -> W}) (x : V).

#[local, non_forgetful_inheritance]
HB.instance Definition _ :=
  GRing.isAdditive.Build _ _ (applyr f x) (@additivel_subproof _ _ _ _ _ _ f x).
#[local, non_forgetful_inheritance]
HB.instance Definition _ :=
  GRing.isScalable.Build _ _ _ _ (applyr f x) (@linearl_subproof _ _ _ _ _ _ f x).

Lemma linearl_continuous:
  continuous (f^~ x).
Proof. have <-: applyr f x = f^~x by []. apply: linear_continuous. Qed. 

Lemma linearl_cvg (u : T -> U) (a : U) :
  u @ F --> a -> (f^~x) \o u @ F --> f a x.
Proof. have <-: applyr f x = f^~x by []. apply: linear_cvg. Qed.

Lemma linearl_is_cvg (u : T -> U) :
  cvg (u @ F) -> cvg (f^~x \o u @ F).
Proof. have <-: applyr f x = f^~x by []. apply: linear_is_cvg. Qed.

Lemma linearl_lim (u : T -> U) :
  cvg (u @ F) -> lim (f^~x \o u @ F) = f (lim (u @ F)) x.
Proof. have <-: applyr f x = f^~x by []. apply: linear_lim. Qed.

End BilinearRContinuous.

Section BilinearLContinuous.
Variable (FF : Filter F) (PF: ProperFilter F) (U V W: finNormedModType C).
Variable (f : {bilinear U -> V -> W}) (x : U).

#[local, non_forgetful_inheritance]
HB.instance Definition _ :=
  GRing.isAdditive.Build _ _ (f x) (@additiver_subproof _ _ _ _ _ _ f x).
#[local, non_forgetful_inheritance]
HB.instance Definition _ :=
  GRing.isScalable.Build _ _ _ _ (f x) (@linearr_subproof _ _ _ _ _ _ f x).

Lemma linearr_continuous:
  continuous (f x).
Proof. exact: linear_continuous. Qed. 

Lemma linearr_cvg (u : T -> V) (a : V):
  u @ F --> a -> (f x) \o u @ F --> f x a.
Proof. exact: linear_cvg. Qed.

Lemma linearr_is_cvg (u : T -> V) :
  cvg (u @ F) -> cvg (f x \o u @ F).
Proof. exact: linear_is_cvg. Qed.

Lemma linearr_lim (u : T -> V) :
  cvg (u @ F) -> lim (f x \o u @ F) = f x (lim (u @ F)).
Proof. exact: linear_lim. Qed.

End BilinearLContinuous.

Lemma linear_to_mx_continuous {U} m n (f : {linear U -> 'M[C]_(m,n)}) :
  continuous f.
Proof.
pose g x := (f (r2v x)); suff <-: g \o v2r = f.
apply: continuous_comp_simp; first by apply: v2r_continuous.
by apply/mxlinear_continuous=>a x y; rewrite /g !linearP.
by apply/funext=>x; rewrite /g/= !v2rK.
Qed.

Lemma linear_to_mx_continuousP {U} m n (f : U -> 'M[C]_(m,n)) :
  linear f -> continuous f.
Proof. move=>lf; rewrite (linearlfE lf); exact: linear_to_mx_continuous. Qed.

Lemma linear_of_mx_continuous {U} m n (f : {linear 'M[C]_(m,n) -> U}) :
  continuous f.
Proof.
pose g x := v2r (f x); suff <-: r2v \o g = f.
apply: continuous_comp_simp; last by apply: r2v_continuous.
by apply/mxlinear_continuous=>a x y; rewrite /g !linearP.
by apply/funext=>x; rewrite /g/= !v2rK.
Qed.

Lemma linear_of_mx_continuousP {U} m n (f : 'M[C]_(m,n) -> U) :
  linear f -> continuous f.
Proof. move=>lf; rewrite (linearlfE lf); exact: linear_of_mx_continuous. Qed.

Lemma closed_linearP {U V} (f : U -> V) (A : set V) :
  linear f -> closed A -> closed (f @^-1` A).
Proof. by move=>lf; apply closed_comp=>x _; apply linear_continuousP. Qed.

Lemma open_linearP {U V} (f : U -> V) (A : set V) :
  linear f -> open A -> open (f @^-1` A).
Proof. by move=>lf; apply open_comp=>x _; apply linear_continuousP. Qed.

Lemma closed_linear {U V} (f : {linear U -> V}) (A : set V) : 
  closed A -> closed (f @^-1` A).
Proof. apply closed_linearP; exact: linearP. Qed. 

Lemma open_linear {U V} (f : {linear U -> V}) (A : set V) : 
  open A -> open (f @^-1` A).
Proof. apply open_linearP; exact: linearP. Qed. 

Lemma closed_to_mx_linearP {U} m n (f : U -> 'M[C]_(m,n)) (A : set 'M[C]_(m,n)):
  linear f -> closed A -> closed (f @^-1` A).
Proof. by move=>lf; apply closed_comp=>x _; apply linear_to_mx_continuousP. Qed.

Lemma closed_to_mx_linear {U} m n (f : {linear U -> 'M[C]_(m,n)}) (A : set 'M[C]_(m,n)):
  closed A -> closed (f @^-1` A).
Proof. apply closed_to_mx_linearP; exact: linearP. Qed.

Lemma open_to_mx_linearP {U} m n (f : U -> 'M[C]_(m,n)) (A : set 'M[C]_(m,n)):
  linear f -> open A -> open (f @^-1` A).
Proof. by move=>lf; apply open_comp=>x _; apply linear_to_mx_continuousP. Qed.

Lemma open_to_mx_linear {U} m n (f : {linear U -> 'M[C]_(m,n)}) (A : set 'M[C]_(m,n)):
  open A -> open (f @^-1` A).
Proof. apply open_to_mx_linearP; exact: linearP. Qed.

Lemma closed_of_mx_linearP {U} m n (f : 'M[C]_(m,n) -> U) (A : set U):
  linear f -> closed A -> closed (f @^-1` A).
Proof. by move=>lf; apply closed_comp=>x _; apply linear_of_mx_continuousP. Qed.

Lemma closed_of_mx_linear {U} m n (f : {linear 'M[C]_(m,n) -> U}) (A : set U):
  closed A -> closed (f @^-1` A).
Proof. apply closed_of_mx_linearP; exact: linearP. Qed.

Lemma open_of_mx_linearP {U} m n (f : 'M[C]_(m,n) -> U) (A : set U):
  linear f -> open A -> open (f @^-1` A).
Proof. by move=>lf; apply open_comp=>x _; apply linear_of_mx_continuousP. Qed.

Lemma open_of_mx_linear {U} m n (f : {linear 'M[C]_(m,n) -> U}) (A : set U):
  open A -> open (f @^-1` A).
Proof. apply open_of_mx_linearP; exact: linearP. Qed.

End LinearContinuous.

Section VOrderFinNormedModTheory.
Context {R : realType} {C : extNumType R} {V : vorderFinNormedModType C}.
Local Notation M := 'rV[C]_(dim V).
Import VectorInternalTheory.

Lemma closed_gev0: closed [set x : V | (0 : V) ⊑ x].
Proof. by case: V=>?[?????????????????[]]. Qed.

Definition v2r_vorderle (x y : M) := r2v x ⊑ r2v y.
(* Definition v2r_vorderlt (x y : M) := r2v x ⊏ r2v y. *)

(* Lemma v2r_vorderlt_def (x y : M): v2r_vorderlt x y = (y != x) && (v2r_vorderle x y).
Proof. by rewrite /v2r_vorderlt lt_def (can_eq r2vK). Qed. *)

Lemma v2r_vorderle_anti : antisymmetric v2r_vorderle.
Proof. by move=>x y; rewrite /v2r_vorderle=>/le_anti/r2v_inj. Qed.

Lemma v2r_vorderle_refl : reflexive v2r_vorderle.
Proof. by move=>x; exact: le_refl. Qed.

Lemma v2r_vorderle_trans : transitive v2r_vorderle.
Proof. by move=>x y z; exact: le_trans. Qed.

#[local]
HB.instance Definition v2r_vorderle_porderMixin := Order.Le_isPOrder.Build 
  ring_display 'rV[C]_(dim V) v2r_vorderle_refl v2r_vorderle_anti v2r_vorderle_trans.

Definition v2r_vorderle_porderType : porderType ring_display :=
  HB.pack 'rV[C]_(dim V) v2r_vorderle_porderMixin.

Lemma v2r_lemx_add2r : forall (z x y : M), x ⊑ y -> x + z ⊑ y + z.
Proof. by move=>z x y; rewrite /Order.le/= /v2r_vorderle !linearD/= levD2r. Qed.

Lemma v2r_lemx_pscale2lP : forall (e : C) (x y : M), 0 < e -> x ⊑ y -> e *: x ⊑ e *: y.
Proof. 
by move=>e x y egt0; rewrite /Order.le/= 
  /v2r_vorderle !linearZ/=; apply: lev_pscale2lP.
Qed.

Lemma v2r_closed_gemx0: closed [set x : M | (0 : M) ⊑ x].
Proof.
rewrite (_ : mkset _ = r2v @^-1` [set x : V | (0 : V) ⊑ x]).
apply: closed_comp=>[? _|]; [apply: r2v_continuous | apply: closed_gev0].
by rewrite predeqE {1}/Order.le/= /v2r_vorderle linear0.
Qed.

Definition v2r_mxcporder := MxCPorder
  v2r_lemx_add2r v2r_lemx_pscale2lP v2r_closed_gemx0.

Lemma nondecreasing_oppv (u_ : V ^nat) :
  nondecreasing_seq (- u_) = nonincreasing_seq u_.
Proof. by rewrite propeqE; split => du x y /du; rewrite levN2. Qed.

Lemma nonincreasing_oppv (u_ : V ^nat) :
  nonincreasing_seq (- u_) = nondecreasing_seq u_.
Proof. by rewrite propeqE; split => du x y /du; rewrite levN2. Qed.

Lemma decreasing_oppv (u_ : V ^nat) :
  decreasing_seq (- u_) = increasing_seq u_.
Proof. by rewrite propeqE; split => du x y; rewrite -du levN2. Qed.

Lemma increasing_oppv (u_ : V ^nat) :
  increasing_seq (- u_) = decreasing_seq u_.
Proof. by rewrite propeqE; split => du x y; rewrite -du levN2. Qed.

Lemma lbounded_by_opp (b : V) (u : V ^nat) :
  lbounded_by (-b) (- u) = ubounded_by b u.
Proof. 
by rewrite propeqE; split => bu i; move: (bu i); 
  rewrite {2}/GRing.opp/= levN2.
Qed.

Lemma ubounded_by_opp (b : V) (u : V ^nat) :
  ubounded_by (-b) (- u) = lbounded_by b u.
Proof. 
by rewrite propeqE; split => bu i; move: (bu i); 
  rewrite {2}/GRing.opp/= levN2.
Qed.

Lemma open_ngev0 : open [set x : V | ~ (0 : V) ⊑ x].
Proof. rewrite openC; apply closed_gev0. Qed.

Lemma open_ngev y :  open [set x : V | ~ y ⊑ x].
Proof.
rewrite (_ : mkset _ = [set t | [set x | ~ (0 : V) ⊑ x] (- y + t)]).
by move: (@addr_continuous _ _ (-y))=>/continuousP/=/(_ _ open_ngev0).
by apply/funext=>x; rewrite /= addrC subv_ge0.
Qed.

Lemma open_nlev0 : open [set x : V | ~ x ⊑ (0 : V)].
Proof.
rewrite (_ : mkset _ = [set t | [set x | ~ (0 : V) ⊑ x] (- t)]).
by move: (@opp_continuous _ V)=>/continuousP/=/(_ _ open_ngev0).
by apply/funext=>x; rewrite /= -{2}oppr0 levN2. 
Qed.

Lemma open_nlev y :  open [set x : V | ~ x ⊑ y].
Proof.
rewrite (_ : mkset _ = [set t | [set x : V | ~ - y ⊑ x] (- t)]).
by move: (@opp_continuous _ V)=>/continuousP/=/(_ _ (open_ngev (-y))).
by apply/funext=>x; rewrite /= levN2.
Qed.

Lemma closed_gev x : closed [set y : V | x ⊑ y ].
Proof. 
set A := ~` [set y : V | ~ (x ⊑ y)].
have ->: (fun x0 : V => is_true (x ⊑ x0)) = A.
by rewrite predeqE /A => y/=; rewrite notK.
rewrite closedC. apply/open_ngev. 
Qed.

Lemma closed_lev x : closed [set y : V | y ⊑ x ].
Proof. 
set A := ~` [set y : V | ~ (y ⊑ x)].
have ->: (fun x0 : V => is_true (x0 ⊑ x)) = A.
by rewrite predeqE /A => y/=; rewrite notK.
rewrite closedC. apply/open_nlev. 
Qed.

Lemma closed_eqv x : closed [set y : V | y = x].
Proof. exact: closed_eq. Qed.
(* rewrite (_ : mkset _ = [set y : V | x ⊑ y ] `&` [set y : V | y ⊑ x ]).
apply: closedI; [apply: closed_gev | apply: closed_lev].
by rewrite predeqE=>v/=; split=>[->//|/andP/le_anti->].
Qed. *)

Lemma lim_gev_near {T : Type} {F : set_system T} {FF : ProperFilter F} 
  (x : V) (u : T -> V) :
    cvg (u @ F) -> (\forall n \near F, x ⊑ u n) -> x ⊑ lim (u @ F).
Proof. by move=> /[swap] /(closed_cvg (fun y => x ⊑ y))P; apply/P/closed_gev. Qed.

Lemma limn_gev_near (x : V) (u : V ^nat) : 
  cvgn u -> (\forall n \near \oo, x ⊑ u n) -> x ⊑ limn u.
Proof. exact: lim_gev_near. Qed.

Lemma lim_lev_near {T : Type} {F : set_system T} {FF : ProperFilter F} 
  (x : V) (u : T -> V) :
    cvg (u @ F) -> (\forall n \near F, u n ⊑ x) -> lim (u @ F) ⊑ x.
Proof. by move=> /[swap] /(closed_cvg (fun y : V => y ⊑ x))P; apply/P/closed_lev. Qed.

Lemma limn_lev_near (x : V) (u : V ^nat) : 
  cvgn u -> (\forall n \near \oo, u n ⊑ x) -> limn u ⊑ x.
Proof. exact: lim_lev_near. Qed.

Lemma lev_lim_near {T : Type} {F : set_system T} {FF : ProperFilter F} 
  (u v : T -> V) :
    cvg (u @ F) -> cvg (v @ F) -> 
      (\forall n \near F, u n ⊑ v n) -> lim (u @ F) ⊑ lim (v @ F).
Proof.
move=> uv cu cv; rewrite -(subv_ge0) -limB//.
apply: lim_gev_near=>//. apply: is_cvgB=>//.
by apply: filterS cv => k; rewrite (subv_ge0).
Qed.

Lemma lev_limn_near (u_ v_ : V ^nat) : cvgn u_ -> cvgn v_ ->
  (\forall n \near \oo, u_ n ⊑ v_ n) -> limn u_ ⊑ limn v_.
Proof. exact: lev_lim_near. Qed.

Lemma lim_gev {T : Type} {F : set_system T} {FF : ProperFilter F} 
  (x : V) (u : T -> V) :
    cvg (u @ F) -> lbounded_by x u -> x ⊑ lim (u @ F).
Proof. by move=>P1 P2; apply: (lim_gev_near P1); apply: nearW. Qed.

Lemma limn_gev (x : V) (u : V ^nat) : cvgn u -> lbounded_by x u -> x ⊑ limn u.
Proof. exact: lim_gev. Qed.

Lemma lim_lev {T : Type} {F : set_system T} {FF : ProperFilter F} 
  (x : V) (u : T -> V) :
    cvg (u @ F) -> ubounded_by x u -> lim (u @ F) ⊑ x.
Proof. by move=>P1 P2; apply: (lim_lev_near P1); apply: nearW. Qed.  

Lemma limn_lev (x : V) (u : V ^nat) : cvgn u -> ubounded_by x u -> limn u ⊑ x.
Proof. exact: lim_lev. Qed.

Lemma lev_lim {T : Type} {F : set_system T} {FF : ProperFilter F} 
  (u v : T -> V) :
    cvg (u @ F) -> cvg (v @ F) -> 
      (forall n, u n ⊑ v n) -> lim (u @ F) ⊑ lim (v @ F).
Proof. by move=>P1 P2 P3; apply: (lev_lim_near P1 P2); apply: nearW. Qed.

Lemma lev_limn (u v : V^nat) : cvgn u -> cvgn v ->
  (forall n, u n ⊑ v n) -> limn u ⊑ limn v.
Proof. exact: lev_lim. Qed.

Lemma nondecreasing_cvgn_lev (u : V ^nat) :
       nondecreasing_seq u -> cvgn u -> ubounded_by (limn u) u.
Proof.
move=>Ph Pc i; apply: limn_gev_near=>//; exists i=>// j; apply Ph.
Qed.

Lemma nonincreasing_cvgn_gev (u : V ^nat) : 
  nonincreasing_seq u -> cvgn u -> lbounded_by (limn u) u.
Proof.
move=>Ph Pc i; apply: limn_lev_near=>//; exists i=>// j; apply Ph.
Qed.

Lemma vnondecreasing_is_cvgn (f : nat -> V) (b : V) :
  nondecreasing_seq f -> ubounded_by b f -> cvgn f.
Proof.
move=>P1 P2. pose g := (v2r \o f).
have P3: nondecreasing_seq g by move=>n m /P1; rewrite {2}/Order.le/= /v2r_vorderle !v2rK.
have P4: ubounded_by (v2r b) g by move=>i; rewrite /Order.le/= /v2r_vorderle !v2rK.
move: (mxnondecreasing_is_cvgn v2r_mxcporder P3 P4).
have <-: r2v \o g = f by apply/funext=>x/=; rewrite v2rK.
move=> /cvg_ex[l fxl]; apply/cvg_ex; exists (r2v l).
by apply: continuous_cvg => //; apply: r2v_continuous.
Qed.

Lemma vnonincreasing_is_cvgn (f : nat -> V) (b : V) :
    nonincreasing_seq f -> lbounded_by b f -> cvgn f.
Proof.
rewrite -(nondecreasing_oppv) -(ubounded_by_opp) -is_cvgNE.
exact: vnondecreasing_is_cvgn.
Qed.

End VOrderFinNormedModTheory.

(* Using Carathéodory to show that, *)
(* exists c, forall x, c * \sum_i `|xi| <= `|\sum_i xi| *)
(* Proof sketch : n dim space *)
(* 1. compact SB := [set x : V | 0 ⊑ x /\ `|x| = 1] *)
(* 2. compact SC := [set x : 'rV_n+1 | forall i, 0 <= xi & \sum_i xi = 1] *)
(* 3. pose TT := fun i : option 'I_n.+1 =>  match i with 
                                            | None => 'rV_n+1 
                                            | Some _ => V end  *)
(* 4. pose TA : forall i, set (TT i) := fun i => match i with
                                            | None => SC 
                                            | Some_ => SB end *)
(* 5. note conv(SB) = [set x | exists f : TT, (forall i, TA i (f i)) /\
      \sum_i f None 0 i *: f Some i = x] *)
(*  according to Carathéodory: x \in conv(SB) <-> 
      x = \sum_(i < n+1) ai xi, \sum ai = 1 & xi \in SB *)
(* 6. conv(SB) is compact by tychonoff theorem *)
(* 7. compact SA := [set r : C | exists x, x \in conv(SB) & `|x| = r] *)
(* 8. exists c > 0, SA c /\ forall r, SA r -> c <= r *)
(* 9. forall 0 ⊑ xi, `|\sum_i xi| >= c * \sum_i `|xi| *)

Section test.
Context {R : realType} {C : extNumType R} {V : vorderFinNormedModType C}.

Import Num.Def Num.Theory.

Lemma compact_ge0_norm1 : compact [set x : V | (0 : V) ⊑ x /\ `|x| = 1].
Proof.
apply: (subclosed_compact _ (compact_norm_le (V := V) (e := 1)))=>[|?/=[] _ ->//].
rewrite (_ : mkset _ = [set x : V | (0 : V) ⊑ x] `&` (fun x=>`|x|) @^-1` [set x : C | x = 1]).
apply: closedI. apply: closed_gev0.
apply: closed_comp=>[? _ |]; [apply: norm_continuous | apply: closed_eq].
by apply/funext=>x /=.
Qed.

(*Lemma tychonoff (I : eqType) (T : I -> topologicalType)
  (A : forall i, set (T i)) :*)
(*T : *)
Let TT (i : option bool) : topologicalType :=
  match i with
  | None => C
  | Some _ => V
  end.
Let TA (i : option bool) : set (TT i) :=
  match i with
  | None => [set x : C | 0 <= x <= 1]
  | Some _ => [set x : V | (0 : V) ⊑ x /\ `|x| = 1]
  end.
Let SV := [set x : V | exists a y z, 0 <= a <= 1 /\ 
((0 : V) ⊑ y /\ `|y| = 1) /\ ((0 : V) ⊑ z /\ `|z| = 1) /\ a *: y + (1-a) *: z = x].
Let SA := [set x : C | exists a y z, 0 <= a <= 1 /\ 
((0 : V) ⊑ y /\ `|y| = 1) /\ ((0 : V) ⊑ z /\ `|z| = 1) /\ `|a *: y + (1-a) *: z| = x].
Let SA_SV : SA = (fun x => `|x|) @` SV.
Proof.
apply/funext=>x/=; rewrite propeqE; split.
move=>[a[y[z[Pa[Py[Pz P]]]]]]; exists (a *: y + (1 - a) *: z)=>//;
exists a; exists y; exists z; do !split=>//.
move=>[w[a[y[z [Pa [Py [Pz <-]]]]]]] <-; exists a; exists y; exists z.
do !split=>//.
Qed.

Lemma compact_citv (a b : C) : compact [set x : C | a <= x <= b].
Proof.
apply: (subclosed_compact _ (extNum_bounded_compact (a := `|b - a| + `|a|))).
rewrite (_ : mkset _ = [set x : C | a <= x] `&` [set x : C | x <= b]).
apply: closedI. apply: etclosed_ge. apply: etclosed_le.
by apply/funext=>x/=; rewrite propeqE; split=>[/andP//|[]->->].
move=>x/=/andP[]; rewrite -[a <= x]subr_ge0 -[x <= b](lerD2r (-a))=>P1 P2.
rewrite -lerBlDr; apply/(le_trans (lerB_dist _ _)).
by rewrite !ger0_norm//; apply: (le_trans P1).
Qed.

Let compact_SV : compact SV.
Proof.
rewrite /SV (_ : mkset _ = (fun x => x None *: x (Some true) + (1 - x None) *: x (Some false)) @` [set f : product_topology_def _ | 
  (forall i : option bool, @TA i (f i))]); last first.
apply/funext=>x/=; rewrite propeqE; split.
move=>[a[y[z[Pa[Py[Pz P]]]]]]; exists ((fun i : option bool => match i with 
  | None => a | Some true => y | Some false => z end) : forall i, TT i)=>//.
by case=>//=; case.
move=>[t Pt1 Pt2]; exists (t None); exists (t (Some true)); exists (t (Some false)).
split; first by apply: (Pt1 None). split; last split=>//; apply: (Pt1 (Some _)).

apply: continuous_compact; last first.
apply: tychonoff; case=>/=. move=>_; apply: compact_ge0_norm1. apply: compact_citv.
move=>x; apply: cvgD; apply: cvgZ.
3: apply: cvgB; first by apply: cvg_cst.
all: move: x; apply: continuous_subspaceT.
1,3: apply: (@proj_continuous _ TT None).
apply: (@proj_continuous _ TT (Some true)).
apply: (@proj_continuous _ TT (Some false)).
Qed.

Let compact_SA : compact SA.
Proof.
rewrite SA_SV; apply: (continuous_compact _ compact_SV).
apply/continuous_subspaceT/norm_continuous.
Qed.

Let not_SA0 : ~ SA 0.
Proof.
move=>[a[y[z[/andP[Pa1 Pa2][[y_ge0 +][[z_ge0 +]]]]]]]/eqP; rewrite normrE addv_ss_eq0.
rewrite !scaler_eq0 -[y == 0]normr_eq0 -[z == 0]normr_eq0=>->->.
by rewrite !oner_eq0 !orbF=>/andP[]/eqP->; rewrite subr0 oner_eq0.
by apply/orP; left; rewrite !scalev_ge0// subr_ge0.
Qed.

Let SA_ge0 (x : C) : SA x -> x > 0.
Proof.
rewrite lt_def=>P1; apply/andP; split.
by apply/negP=>/eqP Px; apply: not_SA0; rewrite -Px.
by move: P1=>[?[?[?[?[?[?]]]]]]<-.
Qed.

Lemma lev_add_norm_lbound : { c : C | 0 < c <= 1 /\ (forall X Y, 
  ((0 : V) ⊑ X) && ((0 : V) ⊑ Y) -> c * (`|X| + `|Y|) <= `|X + Y|)}.
Proof.
move: (pselect (exists x : V, (0 : V) ⊏ x))=>[]; last first.
move=>/forallNP P1; exists 1; split=>[|X Y /andP[]].
by apply/andP; split.
by rewrite le_eqVlt =>/orP[|/P1//]/eqP<-; rewrite normr0 !add0r mul1r.
move=>/cid[x x_gt0].
have Px0 : forall (x : V), (0 : V) ⊏ x -> `|x| > 0.
  by move=>y; rewrite !lt_def normr_eq0=>/andP[]->//=.
have Px: forall (x : V), (0 : V) ⊏ x -> `|1/`|x| *: x| = 1.
  by move=>y /Px0 Py; rewrite normrZ normrM normr1 mul1r 
  gtr0_norm ?invr_gt0// mulVf// lt0r_neq0.
have Ps1: SA 1.
  exists 0; exists (1/`|x| *: x); exists (1/`|x| *: x); do ! split.
  by apply/andP; split. 1,3: by rewrite scalev_ge0// ltW. 1,2: by apply: Px.
  by rewrite scale0r add0r subr0 scale1r Px.
have /cid2[c Pc1 Pc2]: exists2 x : C, SA x & forall y : C, SA y -> x <= y.
  by apply: extNum_compact_min=>[i/SA_ge0/=/gtr0_real//||]; [apply: compact_SA | exists 1].
have cle1 : c <= 1 by apply: Pc2.
exists c; split=>[|X Y]; first by apply/andP; split=>//; apply: SA_ge0.
rewrite 2 !le_eqVlt=>/andP[]/orP[/eqP<- _|X_gt0/orP[/eqP<-|Y_gt0]].
1,2: rewrite !normr0 ?(add0r, addr0) ler_piMl//.
pose a : C := `|X| / (`|X| + `|Y|).
pose Z := a *: (1 / `|X| *: X) + (1-a) *: (1 / `|Y| *: Y).
have PZ: SV Z.
exists a; exists (1 / `|X| *: X); exists (1 / `|Y| *: Y); do ! split.
  by apply/andP; split; rewrite /a ?divr_ge0// ler_pdivrMr 
    ?mul1r ?lerDl// addr_gt0// Px0.
  1,3: by rewrite scalev_ge0// ltW.
  1,2: by apply: Px.
have: SA `|Z| by rewrite SA_SV/=; exists Z.
move=>/Pc2; rewrite/Z !scalerA.
have ->: a * (1 / `|X|) = 1 / (`|X| + `|Y|).
  by rewrite/a mulrC mulrA mulfVK// lt0r_neq0// Px0.
have ->: (1 - a) * (1 / `|Y|) = 1 / (`|X| + `|Y|).
  rewrite -{1}(mulfV (x := `|X| + `|Y|)) ?lt0r_neq0// ?addr_gt0// ?Px0//.
  by rewrite /a -mulrBl addrC addKr mulrC mulrA mulfVK// lt0r_neq0// Px0.
by rewrite -scalerDr normrZ ger0_norm ?divr_ge0// 
  mulrC mulrA mulr1 ler_pdivlMr// addr_gt0// Px0.
Qed.

(* Lemma test7 (x y : V) : `|x| = 1 -> `|y| <= 1 -> exists a z, 
  0 <= a <= 1 /\ `|z| = 1 /\ a *: x + (1-a) *: z = y.
Admitted.

Lemma test6 : { c : C | c > 0 /\ 
  (forall X Y, ((0 : V) ⊑ X) && (X ⊑ Y) -> c * `|X| <= `|Y|)}.
move: (pselect (exists x : V, (0 : V) ⊏ x))=>[]; last first.
move=>/forallNP P1; exists 1; split=>// X Y.
by move=>/andP[] xge0 /(le_trans xge0); move: xge0; rewrite !le_eqVlt
  =>/orP[|/P1//]/eqP<-/orP[|/P1//]/eqP<-; rewrite !normr0 mulr0 eqxx.
move=>/cid[x xgt0].
have Px: `|1/`|x| *: x| = 1.
  rewrite normrZ normrM normr1 mul1r ger0_norm ?invr_ge0// mulVf//.
  by move: xgt0; rewrite lt_def normr_eq0=>/andP[].
have Ps1: SA 1.
  exists 0; exists (1/`|x| *: x); exists (1/`|x| *: x); do ! split=>//.
  by apply/andP; split. 1,2: by rewrite scalev_ge0// ltW.
  by rewrite scale0r add0r subr0 scale1r.
have /cid2[c Pc1 Pc2]: exists2 x : C, SA x & forall y : C, SA y -> x <= y.
by apply: extNum_compact_min=>[i/test5/=/gtr0_real//||]; [apply: test3 | exists 1].
have cle1 : c <= 1 by apply: Pc2.
exists c; split=>[|X Y]. by apply: test5.
case E: (X == 0); first by move: E=>/eqP->; rewrite normr0 mulr0. *)

End test.

Module R_extNumType.

Section R_extNumType.
Variable (R : realType).

Program Definition R_extNumMixin := @NumField_isExtNum.Build R R 
  (idfun : R -> R) (idfun : R -> R) _ _ _ _ _ _ .
Next Obligation. by []. Qed.
Next Obligation. by []. Qed.
Next Obligation. by []. Qed.
Next Obligation. by move=>x. Qed.
Next Obligation. by []. Qed.
Next Obligation. move=>a.
rewrite (_ : mkset _ = [set x : R | x \in `[-a,a]]); first apply: segment_compact.
by rewrite predeqE=>x/=; rewrite itv_boundlr/= [in X in _ <-> X]/<=%O/= Num.Theory.ler_norml.
Qed.

HB.instance Definition _ := R_extNumMixin.

End R_extNumType.

End R_extNumType.
Export R_extNumType.