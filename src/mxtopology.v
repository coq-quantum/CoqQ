From mathcomp Require Import all_ssreflect all_algebra.
Require Import forms.
From mathcomp.analysis Require Import boolp ereal reals cardinality mathcomp_extra.
From mathcomp.analysis Require Import 
  signed classical_sets functions topology prodnormedzmodule normedtype sequences.
From mathcomp.real_closed Require Import complex.
Require Import mcextra mxpred hermitian.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order Order.Theory GRing.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(* compact R set has maximum and minimum *)
Section R_compact_max_min.
Variable (R: realType).
Import Num.Theory numFieldNormedType.Exports.

Lemma compact_max (S: set R) : 
  compact S -> S !=set0 -> exists2 x, S x & (forall y, S y -> y <= x).
Proof.
move=>P1 P2; move: {+}P2=>[x Px].
have PF : ProperFilter (globally S) by apply: (@globally_properfilter _ _ x).
have ubS : has_ubound S.
move: P1=>/compact_bounded/=/(ex_bound)/==>[[M PM]].
exists M=>y Py; apply: (le_trans (ler_norm _)); by apply PM.
exists (sup S); last by apply/ubP/sup_upper_bound; split.
by move: (compact_closed (@Rhausdorff R) P1)=>/closure_id{1}->; apply closure_sup.
Qed.

Lemma compact_min (S: set R) : 
  compact S -> S !=set0 -> exists2 x, S x & (forall y, S y -> x <= y).
Proof.
move=>P1 P2; have cS : compact [set - x | x in S]
  by apply/continuous_compact=>//; apply/continuous_subspaceT=>x _; apply: opp_continuous.
have nS : [set - x | x in S] !=set0 by by apply nonemptyN.
have inS: forall x, [set - x | x in S] (-x) <-> S x.
move=>x; split=>[[y Py /oppr_inj<-//]|Px]; by exists x.
move: (compact_max cS nS)=>[x Px lex].
exists (- x)=>[|y]; first by rewrite -inS opprK.
by rewrite -inS Num.Theory.ler_oppl =>/lex.
Qed.
End R_compact_max_min.

(* Prove the completeness of C *)
Module CTopology.

Section CTopology.
Import GRing.Theory ComplexField Order.TTheory.
Import Pointed.Exports Filtered.Exports Topological.Exports Uniform.Exports PseudoMetric.Exports.
Import Complete.Exports CompletePseudoMetric.Exports.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Variable (R: realType).
Local Notation C := R[i].
Local Canonical C_pointedType := [pointedType of C for [pointedType of C^o]].
Local Canonical C_filteredType := [filteredType C of C for [filteredType C of C^o]].
Local Canonical C_topologicalType := [topologicalType of C for [topologicalType of C^o]].
Local Canonical C_uniformType := [uniformType of C for [uniformType of C^o]].
Local Canonical C_pseudoMetricType := [pseudoMetricType [numDomainType of C] of C for [pseudoMetricType [numDomainType of C] of C^o]].
Local Canonical C_pseudoMetricNormedZmodType := [pseudoMetricNormedZmodType C of C for [pseudoMetricNormedZmodType C of C^o]].
Local Canonical C_normedModType := [normedModType C of C for [normedModType C of C^o]].
Local Open Scope classical_set_scope.
Local Open Scope complex_scope.
Local Open Scope ring_scope.

Lemma C_complete (F : set (set C)) : ProperFilter F -> cauchy F -> cvg F.
Proof.
move=> FF /cauchyP F_cauchy. 
suff P1: cauchy (fmap (@Re _) F).
suff P2: cauchy (fmap (@Im _) F).
move: (R_complete (fmap_proper_filter (@Re _) FF) P1) (R_complete (fmap_proper_filter (@Im _) FF) P2)=>
/cvg_ex[relim /(@cvg_dist _ _ _ (fmap_proper_filter (@Re _) FF)) cvgRe] 
/cvg_ex[imlim /(@cvg_dist _ _ _ (fmap_proper_filter (@Im _) FF)) cvgIm].
apply/cvg_ex=>/=; exists (relim +i* imlim).
apply: (cvg_distW)=>/= e egt0; move: (real_gt0 egt0)=>ree.
have regt0 : (Re e) / 2%:R > 0 by apply cauchyreals.divrn_gt0. 
move: (cvgRe _ regt0) (cvgIm _ regt0). 
rewrite /prop_near1 !nbhs_filterE/= !nbhs_filterE/= =>P3 P4.
move: (@filterI _ _ FF _ _ P3 P4)=>P5.
apply: (@filterS _ _ FF _ _ _ P5) => x /=; rewrite normc_def/= !linearB/=.
  rewrite -{3}(cgt0_real egt0) lecR -(Num.Theory.gtr0_norm regt0) -{3}(Num.Theory.gtr0_norm ree)
    -!Num.Theory.sqrtr_sqr !Num.Theory.ltr_sqrt ?Num.Theory.ler_sqrt.
  move=>[Pt1] /(Num.Theory.ltr_add Pt1) Pt2; apply/ltW; apply (lt_trans Pt2).
  by rewrite {3}(mathcomp_extra.splitr (Re e)) sqrrD addrC addrA Num.Theory.ltr_addl mulr2n 
    Num.Theory.addr_gt0//; apply Num.Theory.mulr_gt0.
  1,2,3: by apply Num.Theory.exprn_gt0.
all: apply/cauchyP; move: F_cauchy; rewrite /cauchy_ex/= =>P e egt0;
have ecgt0 : 0 < e%:C by move: egt0; rewrite -ltcR.
all: move: (P _ ecgt0)=>[x Px]. 1: exists (Im x). 2: exists (Re x).
all: apply: (filterS _ Px)=>y; rewrite /ball/= normc_def ltcR=>Pt;
apply: (le_lt_trans _ Pt); rewrite !linearB/= -Num.Theory.sqrtr_sqr;
apply Num.Theory.ler_wsqrtr; by rewrite ?Num.Theory.ler_addl 
?Num.Theory.ler_addr Num.Theory.sqr_ge0.
Qed.

Local Canonical C_completeType :=
  CompleteType C (@C_complete).
Local Canonical C_CompleteNormedModule :=
  [completeNormedModType C of C].

End CTopology.

Module Exports.
Canonical C_pointedType.
Canonical C_filteredType.
Canonical C_topologicalType.
Canonical C_uniformType.
Canonical C_pseudoMetricType.
Canonical C_pseudoMetricNormedZmodType.
Canonical C_normedModType.
Canonical C_completeType.
Canonical C_CompleteNormedModule.
End Exports.
End CTopology.
Import CTopology.Exports.

(*Cauchy Seq Characterization*)
Section CauchySeq.
Import Num.Def Num.Theory.
Variable (R: numFieldType) (V: completeNormedModType R).

(* to use cauchy_seq for other functions *)
Definition cauchy_seq  (u: nat -> V) := 
  forall e : R, 0 < e -> exists N : nat, 
    forall s t, (N <= s)%N -> (N <= t)%N -> `| u s - u t | < e.

Lemma cauchy_seqP  (u: nat -> V) : cauchy_seq u <-> cvg u.
Proof.
split=>[P1|/cvg_cauchy/cauchyP].
  apply: (@cauchy_cvg _ [filter of u]); apply/cauchyP.
  rewrite /cauchy_ex=>e egt0 /=; move: (P1 _ egt0)=>[N Pn].
  exists (u N); exists N=>// s/= Ps.
  rewrite -ball_normE/=; apply Pn=>//.
rewrite /cauchy_ex=>P e egt0 /=.
have: e / 2%:R > 0 by rewrite divr_gt0// ltr0n.
move/(P _) =>[x /= [N _ PN]]; exists N=>s t Ps Pt.
move: (PN s) (PN t)=>/= /(_ Ps) P1 /(_ Pt) P2.
by move: (ball_splitr P1 P2); rewrite -ball_normE.
Qed.

(* to use cauchy_seq for other functions *)
Definition cvg_seq  (u: nat -> V) a := 
  forall e : R, 0 < e -> exists N : nat, 
    forall s, (N <= s)%N -> `| a - u s | < e.

Lemma cvg_seqP  (u: nat -> V) a : cvg_seq u a <-> u --> a.
Proof.
split=>[P1|/cvg_dist +e egt0].
apply: cvg_distW=>/= e egt0; rewrite/prop_near1 nbhs_filterE/=.
by move: (P1 _ egt0)=>[N PN]; exists N=>//= i/=/PN/ltW.
move=>/(_ e egt0); rewrite/prop_near1 nbhs_filterE=>[[N _ PN]].
by exists N=>n Pn; move: (PN n)=>/=/(_ Pn).
Qed.

Lemma nchain_ge (h: nat -> nat) :
  (forall n, (h n.+1 > h n)%N) -> forall n, (h n >= n)%N.
Proof. by move=>P1 n; elim: n=>[|n IH]; [rewrite leq0n| apply/(leq_ltn_trans IH)]. Qed.

Lemma nchain_mono (h: nat -> nat) :
  (forall n, (h n.+1 > h n)%N) -> forall n m, (n > m)%N -> (h n > h m)%N.
Proof.
move=>P1 n m; elim: n=>// n IH /ltnSE. 
rewrite leq_eqVlt=>/orP[/eqP->//|/IH H].
by apply (ltn_trans H).
Qed.

Fixpoint nseq_sig Q (P : forall n, {m : nat | Q n m}) m :=
  match m with
  | O => projT1 (P O)
  | S n => projT1 (P (nseq_sig P n))
  end.

Lemma nseq_sigE Q (P : forall n, {m : nat | Q n m}) m :
  nseq_sig P m.+1 = projT1 (P (nseq_sig P m)).
Proof. by []. Qed.

Lemma nseq_sigP Q (P : forall n, {m : nat | Q n m}) (m:nat) :
  Q (nseq_sig P m) (projT1 (P (nseq_sig P m))).
Proof. by move: (projT2 (P (nseq_sig P m))). Qed.

Lemma implyE (P Q : Prop) : (P -> Q) = ~ P \/ Q.
Proof. by rewrite -(notK (P -> Q)) not_implyE propeqE not_andP notK. Qed.

Lemma implyNE (P Q : Prop) : (P -> ~ Q) = (~ (P /\ Q)).
Proof. by rewrite implyE propeqE not_andP. Qed.

(* not exists subseq -> there is a bound *)
Lemma non_exists_nseq (P : nat -> Prop) :
  ~ (exists (h : nat -> nat), (forall n, (h n.+1 > h n)%N) /\ (forall n, P (h n)))
  -> exists N, forall n, (n >= N)%N -> ~ (P n).
Proof.
apply contra_notP. rewrite not_existsP !notK=>H.
suff H1: forall n, {m : nat | (n < m /\ P m)%N}.
exists (nseq_sig H1); split=>n.
by move: (nseq_sigP H1 n)=>[+_]; rewrite nseq_sigE.
rewrite /=; case: n=>[|n]. 
by rewrite /nseq_sig; move: (projT2 (H1 0%N))=>[].
by rewrite nseq_sigE; move: (projT2 (H1 (nseq_sig H1 n)))=>[].
move=>n; apply/cid; move: (H n.+1); apply contra_notP; 
by rewrite not_existsP notK=>H1 m; move: (H1 m); rewrite -implyNE.
Qed.

Lemma cvg_limP (f: nat -> V) (a: V) :
  f --> a <-> forall e, 0 < e -> exists N, forall n,  (N <= n)%N -> `|f n - a| < e.
Proof.
rewrite cvg_ballP; split=>+e egt0; move=>/(_ e egt0); rewrite near_map=>[[N Pn]].
move=>P1; exists N=>n ltNn; move: (P1 n)=>/=. 
2: exists N=>// n/=/Pn.
all: rewrite -ball_normE/= -Num.Theory.normrN opprB// =>P2.
by apply P2.
Qed.

Lemma cvg_subseqP (f: nat -> V) (a: V) : 
  f --> a <-> (forall (h: nat -> nat), (forall n, (h n.+1 > h n)%N) -> (f \o h) --> a).
Proof.
split=>[|H].
rewrite cvg_limP=>H h Ph; rewrite cvg_limP=>e egt0.
move: (H _ egt0)=>[N H1]; exists N=>n IH.
apply H1; by apply/(leq_trans IH)/nchain_ge.
have /H: forall n, (id n < id n.+1)%N by [].
suff ->: f \o id = f by []. by apply/funext=>n.
Qed.

Lemma cvg_subseqPN (f: nat -> V) (a: V) :
  ~ (f --> a) <-> exists e (h: nat -> nat), 
    (forall n, (h n.+1 > h n)%N) /\ 0 < e /\ (forall n, `|(f \o h) n - a| >= e).
split; last first.
- apply contraPnot. rewrite -forallNP.
  move=>/cvg_limP H1 e. rewrite -forallNP=>h [P1 [P2]] /not_forallP P3.
  apply P3. move: (H1 _ P2)=>[N PN]. exists N.+1. apply/negP.
  rewrite -real_ltNge//= ?gtr0_real//. apply/PN.
  by apply: (leq_trans _ (nchain_ge P1 _)).
rewrite cvg_limP -existsNE=>[[e]].
rewrite not_implyP -forallNP=>[[egt0 P]].
exists e. pose P1 n := (e <= `|f n - a|) : Prop.
suff: (exists h, (forall n, (h n.+1 > h n)%N) /\ (forall n, P1 (h n))).
by move=>[h [Ph1 Ph2]]; exists h; split=>//.
move: P; apply contraPP=>/non_exists_nseq[N PN].
rewrite not_forallP notK; exists N; rewrite notK=>n/PN.
by rewrite /P1=>/negP; rewrite -real_ltNge// gtr0_real.
Qed.

Lemma cvg_limE (f: nat -> V) (a: V) : hausdorff_space V -> f --> a <-> lim f = a /\ cvg f.
Proof. 
split=>[P1|[ <-]//]. split. apply/cvg_lim. apply H.
apply P1. by move: P1=>/cvgP.
Qed.

End CauchySeq.

(* I don't know why cvgD ... are difficult to use;   *)
(* maybe due to the canonical of R[i]?               *)
(* for convenience, I write some of the theorems here*)
Section complex_seq_composition.
Variable (R: realType).
Local Notation C := R[i].
Implicit Type (f g: nat -> C) (n: nat) (s a b : C).

Lemma Chausdorff : hausdorff_space [topologicalType of C].
Proof. apply: norm_hausdorff. Qed.

Lemma ccvg_limE f a : f --> a <-> lim f = a /\ cvg f.
Proof. exact: (cvg_limE f a Chausdorff). Qed.

Lemma ccvg_cst a : (fun n:nat=>a) --> a. Proof. exact: cvg_cst. Qed.
Lemma is_ccvg_cst a : cvg (fun n:nat=>a). Proof. exact: is_cvg_cst. Qed.
Lemma clim_cst a : lim (fun n:nat=>a) = a. Proof. exact: lim_cst. Qed.
Lemma ccvgN f a : f --> a -> (- f) --> - a. Proof. exact: cvgN. Qed.
Lemma is_ccvgN f : cvg f -> cvg (- f). Proof. exact: is_cvgN. Qed.
Lemma is_ccvgNE f : cvg (- f) = cvg f. Proof. exact: is_cvgNE. Qed.
Lemma ccvgMn f n a : f --> a -> ((@GRing.natmul _)^~n \o f) --> a *+ n. Proof. exact: cvgMn. Qed.
Lemma is_ccvgMn f n : cvg f -> cvg ((@GRing.natmul _)^~n \o f). Proof. exact: is_cvgMn. Qed.
Lemma ccvgD f g a b : f --> a -> g --> b -> (f + g) --> a + b. Proof. exact: cvgD. Qed.
Lemma is_ccvgD f g : cvg f -> cvg g -> cvg (f + g). Proof. exact: is_cvgD. Qed.
Lemma ccvgB f g a b : f --> a -> g --> b -> (f - g) --> a - b. Proof. exact: cvgB. Qed.
Lemma is_ccvgB f g : cvg f -> cvg g -> cvg (f - g). Proof. exact: is_cvgB. Qed.
Lemma is_ccvgDlE f g : cvg g -> cvg (f + g) = cvg f. Proof. exact: is_cvgDlE. Qed.
Lemma is_ccvgDrE f g : cvg f -> cvg (f + g) = cvg g. Proof. exact: is_cvgDrE. Qed.
Lemma ccvgM f g a b : f --> a -> g --> b -> (f * g) --> a * b. Proof. exact: cvgZ. Qed.
Lemma is_ccvgM f g : cvg f -> cvg g -> cvg (f * g). Proof. exact: is_cvgZ. Qed.
Lemma ccvgMl f a b (g := fun=>b): f --> a -> f * g --> a * b. Proof. exact: cvgZl. Qed.
Lemma ccvgMr g a b (f := fun=>a): g --> b -> f * g --> a * b. Proof. exact: cvgZr. Qed.
Lemma is_ccvgMr g a (f := fun=> a) : cvg g -> cvg (f * g). Proof. exact: is_cvgZr. Qed.
Lemma is_ccvgMrE g a (f := fun=> a) : a != 0 -> cvg (f * g) = cvg g. Proof. exact: is_cvgZrE. Qed.
Lemma is_ccvgMl f a (g := fun=> a) : cvg f -> cvg (f * g). Proof. exact: is_cvgMl. Qed.
Lemma is_ccvgMlE f a (g := fun=> a) : a != 0 -> cvg (f * g) = cvg f. Proof. exact: is_cvgMlE. Qed.
Lemma ccvg_norm f a : f --> a -> (Num.norm \o f) --> `|a|. Proof. exact: cvg_norm. Qed.
Lemma is_ccvg_norm f : cvg f -> cvg (Num.norm \o f). Proof. exact: is_cvg_norm. Qed.
Lemma climN f : cvg f -> lim (- f) = - lim f. Proof. exact: limN. Qed.
Lemma climD f g : cvg f -> cvg g -> lim (f + g) = lim f + lim g. Proof. exact: limD. Qed.
Lemma climB f g : cvg f -> cvg g -> lim (f - g) = lim f - lim g. Proof. exact: limB. Qed.
Lemma climM f g : cvg f -> cvg g -> lim (f * g) = lim f * lim g. Proof. exact: limM. Qed.
Lemma clim_norm f : cvg f -> lim (Num.norm \o f) = `|lim f|. Proof. exact: lim_norm. Qed.
Lemma climV f : cvg f -> lim f != 0 -> lim ((fun x => (f x)^-1)) = (lim f)^-1. Proof. exact: limV. Qed.

Lemma ccvg_map f a (V : completeType) (h : C -> V) :
  continuous h -> f --> a -> (h \o f) --> h a.
Proof. 
move=>ch cvgf; apply: (@cvg_fmap _ _ [filter of f] a h).
by apply ch. by apply cvgf.
Qed.

Lemma ccvg_mapV (V : completeType) (h : V -> C) (h' : nat -> V) (a : V) :
  continuous h -> h' --> a -> (h \o h') --> h a.
Proof. 
move=>ch cvgf; apply: (@cvg_fmap _ _ [filter of h'] a h).
by apply ch. by apply cvgf.
Qed.

Lemma is_ccvg_map f (V : completeType) (h : C -> V) :
  continuous h -> cvg f -> cvg (h \o f).
Proof.
move=>P1 /cvg_ex=>[/= [a Pa]]. apply/cvg_ex.
exists (h a). by move: (ccvg_map P1 Pa).
Qed.

Lemma is_ccvg_mapV (V : completeType) (h : V -> C) (h' : nat -> V) :
  continuous h -> cvg h' -> cvg (h \o h').
Proof.
move=>P1 /cvg_ex=>[/= [a Pa]]. apply/cvg_ex.
exists (h a). by move: (ccvg_mapV P1 Pa).
Qed.

Lemma clim_map f a (V : completeType) (h : C -> V) :
  hausdorff_space V -> continuous h -> cvg f -> lim (h \o f) = h (lim f).
Proof. by move=>hV ch; move/(ccvg_map ch)/cvg_lim=>/(_ hV). Qed.

Lemma clim_mapV (V : completeType) (h : V -> C) (h' : nat -> V) :
  continuous h -> cvg h' -> lim (h \o h') = h (lim h').
Proof. by move=>ch; move/(ccvg_mapV ch)/cvg_lim=>/(_ Chausdorff). Qed.

Lemma ccvg_limP f a :
  f --> a <-> forall e, 0 < e -> exists N, forall n,  (N <= n)%N -> `|f n - a| < e.
Proof. exact: cvg_limP. Qed.

Lemma ccvg_subseqP f a : 
  f --> a <-> (forall (h: nat -> nat), (forall n, (h n.+1 > h n)%N) -> (f \o h) --> a).
Proof. exact: cvg_subseqP. Qed.

Lemma ccvg_subseqPN f a :
  ~ (f --> a) <-> exists e (h: nat -> nat), 
    (forall n, (h n.+1 > h n)%N) /\ 0 < e /\ (forall n, `|(f \o h) n - a| >= e).
Proof. exact: cvg_subseqPN. Qed.

Definition ccauchy_seq f := forall e, 0 < e -> exists N, forall i j, 
  (N <= i)%N -> (N <= j)%N -> `| f i - f j | < e.

Lemma ccauchy_seqP f : ccauchy_seq f <-> cvg f.
Proof. exact: cauchy_seqP. Qed.

Definition ccvg_seq f a := 
  forall e, 0 < e -> exists N : nat, 
    forall i, (N <= i)%N -> `| a - f i | < e.

Lemma ccvg_seqP f a : ccvg_seq f a <-> f --> a.
Proof. exact: cvg_seqP. Qed.

Lemma re_continuous : continuous (@Re R).
Proof. 
move=> x s/= /nbhs_ballP [/=e egt0 Pb].
apply/nbhs_ballP. exists e%:C =>//=. by rewrite ltcR.
move=> y /= Pxy. apply (Pb (Re y)). move: Pxy.
rewrite -ball_normE/= /ball/= -raddfB/= -ltcR.
apply: (le_lt_trans (normc_ge_Re _)).
Qed.

Lemma im_continuous : continuous (@Im R).
Proof. 
move=> x s/= /nbhs_ballP [/=e egt0 Pb].
apply/nbhs_ballP. exists e%:C =>//=. by rewrite ltcR.
move=> y /= Pxy. apply (Pb (Im y)). move: Pxy.
rewrite -ball_normE/= /ball/= -raddfB/= -ltcR.
apply: (le_lt_trans (normc_ge_Im _)).
Qed.

Lemma rc_continuous : continuous (@real_complex R).
Proof. 
move=> x s/= /nbhs_ballP [/=e egt0 Pb].
apply/nbhs_ballP. exists (Re e) =>//=. by apply real_gt0.
move=> y /= Pxy. apply (Pb y%:C). move: Pxy.
by rewrite -ball_normE/= /ball/= -raddfB/= -ltcR cgt0_real// normc_real.
Qed.

Lemma ic_continuous : continuous (@im_complex R).
Proof. 
move=> x s/= /nbhs_ballP [/=e egt0 Pb].
apply/nbhs_ballP. exists (Re e) =>//=. by apply real_gt0.
move=> y /= Pxy. apply (Pb y%:Ci). move: Pxy.
rewrite -ball_normE/= /ball/= -(@raddfB _ _ (im_complex_additive R))/=.
by rewrite normc_im -ltcR cgt0_real// normc_real.
Qed.

Lemma cseq_split (u : C ^nat) : ((@real_complex R) \o ((@Re R) \o u)) + 
  ((@im_complex R) \o ((@Im R) \o u)) = u.
Proof. by apply/funext=>i; rewrite /GRing.add/= complex_split. Qed.

Lemma conjC_continuous (K : numClosedFieldType) : continuous (@Num.Theory.conjC K).
Proof.
move=> x s/= /nbhs_ballP [/=e egt0 Pb].
apply/nbhs_ballP. exists (e) =>//=.
move=> y /= Pxy. apply (Pb (@Num.Theory.conjC K y)). move: Pxy.
by rewrite /ball/= -rmorphB Num.Theory.norm_conjC.
Qed.
Lemma ccvg_conj f a : f --> a -> (Num.Theory.conjC \o f) --> (Num.Theory.conjC a).
Proof. by apply: continuous_cvg; apply conjC_continuous. Qed.
Lemma is_ccvg_conj f : cvg f -> cvg (Num.Theory.conjC \o f).
Proof. by move=> /ccvg_conj /cvgP. Qed.
Lemma is_ccvg_conjE f : cvg (Num.Theory.conjC \o f) = cvg f.
Proof. 
rewrite propeqE; split.
have P1: f = (Num.Theory.conjC \o (Num.Theory.conjC \o f))
by apply/funext=>x/=; rewrite Num.Theory.conjCK.
rewrite [in X in _ -> X]P1. all: apply is_ccvg_conj.
Qed.
Lemma clim_conj f : cvg f -> lim (Num.Theory.conjC \o f) = Num.Theory.conjC (lim f).
Proof. by move=> ?; apply: cvg_lim; [apply: Chausdorff | apply: ccvg_conj]. Qed.

End complex_seq_composition.

Lemma compA U V W T (f: U -> V) (g : V -> W) (h : W -> T) :
  h \o (g \o f) = h \o g \o f.
Proof. exact. Qed.

Section complex_monotone.
Variable (R : realType).
Local Notation C := R[i].

Lemma cnondecreasing_split (u_ : C ^nat) :
  nondecreasing_seq u_ <-> (nondecreasing_seq ((@Re _) \o u_)) /\ 
    (@Im _) \o u_ = (fun=> Im (u_ 0%N)).
Proof.
split=>[homc|[homr csti m n /homr]]/=.
split=>[m n /homc|]/=. by rewrite lecE=>/andP[_].
apply/funext=>n. move: (homc _ _ (leq0n n)). by rewrite lecE/==>/andP[/eqP->].
move: csti. rewrite lecE funeqE=> Pi->.
move: (Pi n) (Pi m)=>/=-> ->. by rewrite eqxx.
Qed.

Lemma cubounded_split (u_ : C ^nat) (M : C):
  (forall n : nat, u_ n <= M) <-> (forall n : nat, ((@Re _) \o u_) n <= Re M) /\ 
    (@Im _) \o u_ = (fun=> Im M).
Proof.
split=>[ub|[ubr csti]]. split.
move=>n. move: (ub n)=>/=. by rewrite lecE/==>/andP[_].
apply/funext=>n. move: (ub n).
by rewrite !lecE/==>/andP[/eqP<- _].
move=>n. move: csti. rewrite lecE funeqE=>csti.
by move: (ubr n) (csti n)=>/=->/esym/eqP->.
Qed.

Lemma cnonincreasing_split (u_ : C ^nat) :
  nonincreasing_seq u_ <-> (nonincreasing_seq ((@Re _) \o u_)) /\ 
    (@Im _) \o u_ = (fun=> Im (u_ 0%N)).
Proof.
split=>[homc|[homr csti m n /homr]]/=.
split=>[m n /homc|]/=. by rewrite lecE=>/andP[_].
apply/funext=>n. move: (homc _ _ (leq0n n)). by rewrite lecE/==>/andP[/eqP->].
move: csti. rewrite lecE funeqE=> Pi->.
move: (Pi n) (Pi m)=>/=-> ->. by rewrite eqxx.
Qed.

Lemma clbounded_split (u_ : C ^nat) (M : C):
  (forall n : nat, M <= u_ n) <-> (forall n : nat, Re M <= ((@Re _) \o u_) n) /\ 
    (@Im _) \o u_ = (fun=> Im M).
Proof.
split=>[ub|[ubr csti]]. split.
move=>n. move: (ub n)=>/=. by rewrite lecE/==>/andP[_].
apply/funext=>n. move: (ub n).
by rewrite !lecE/==>/andP[/eqP<- _].
move=>n. move: csti. rewrite lecE funeqE=>csti.
by move: (ubr n) (csti n)=>/=->/eqP->.
Qed.

Lemma ccvg_split (u_ : C ^nat) :
  cvg u_ -> cvg ((@Re _) \o u_) /\ cvg ((@Im _) \o u_).
Proof. split; apply/is_ccvg_map=>//; [apply re_continuous| apply im_continuous]. Qed.

Lemma clim_split (u_ : C ^nat) :
  cvg u_ -> lim u_ = (lim ((@Re _) \o u_))%:C + (lim ((@Im _) \o u_))%:Ci.
Proof.
move=>Pcvg; move: Pcvg {+}Pcvg.
move=>/(ccvg_map (@re_continuous R))/(cvg_lim (@Rhausdorff _))->.
move=>/(ccvg_map (@im_continuous R))/(cvg_lim (@Rhausdorff _))->.
by rewrite complex_split.
Qed.


Lemma cnondecreasing_is_cvg (u_ : C ^nat) (M : C) :
       nondecreasing_seq u_ -> (forall n : nat, u_ n <= M) -> cvg u_.
Proof.
move/cnondecreasing_split=>[P1 P2] /cubounded_split [P3 _].
rewrite -(cseq_split u_). apply/is_ccvgD; apply is_ccvg_mapV=>//.
apply rc_continuous. apply: (nondecreasing_is_cvg P1 _). by exists (Re M) => _ [n _ <-].
apply ic_continuous. rewrite P2. apply: is_cvg_cst.
Qed.

Lemma cnondecreasing_cvg (u_ : C ^nat) (M : C) :
       nondecreasing_seq u_ -> (forall n : nat, u_ n <= M) -> 
        u_ --> (lim ((@Re _) \o u_))%:C + (Im M)%:Ci.
Proof.
move=>P1 P2. move: (cnondecreasing_is_cvg P1 P2)=>P3.
rewrite ccvg_limE; split=>//. rewrite clim_split//.
move: P2=>/cubounded_split [_ P4]. rewrite P4 lim_cst//. 
apply Rhausdorff.
Qed.

Lemma cnonincreasing_is_cvg (u_ : C ^nat) (M : C) :
       nonincreasing_seq u_ -> (forall n : nat, M <= u_ n) -> cvg u_.
Proof.
rewrite -nondecreasing_opp -is_ccvgNE =>P1 P2.
apply: (@cnondecreasing_is_cvg _ (- M) P1 _)=>n.
by rewrite {1}/GRing.opp/= Num.Theory.ler_opp2.
Qed.

Lemma cnonincreasing_cvg (u_ : C ^nat) (M : C) :
       nonincreasing_seq u_ -> (forall n : nat, M <= u_ n) -> 
        u_ --> (lim ((@Re _) \o u_))%:C + (Im M)%:Ci.
Proof.
move=>P1 P2. move: (cnonincreasing_is_cvg P1 P2)=>P3.
rewrite ccvg_limE; split=>//. rewrite clim_split//.
move: P2=>/clbounded_split [_ P4]. rewrite P4 lim_cst//. 
apply Rhausdorff.
Qed.

Lemma cnondecreasing_cvg_le (u_ : C ^nat) :
       nondecreasing_seq u_ -> cvg u_ -> (forall n : nat, u_ n <= lim u_).
Proof.
move/cnondecreasing_split=>[P1 P2] P0.
move: P0 {+}P0=>/ccvg_split[P3 _] /clim_split-> n.
rewrite lecE/= P2/= lim_cst ?addr0 ?add0r; last by apply Rhausdorff.
apply/andP; split; first by move: P2; rewrite funeqE=>/(_ n)/=->.
by apply: nondecreasing_cvg_le.
Qed.

Lemma cnonincreasing_cvg_ge (u_ : C ^nat) : 
  nonincreasing_seq u_ -> cvg u_ -> (forall n, lim u_ <= u_ n).
Proof.
rewrite -nondecreasing_opp -is_ccvgNE =>P1 P2 n.
rewrite -(opprK u_) climN// Num.Theory.ler_opp2.
by apply cnondecreasing_cvg_le.
Qed.

Lemma Cnng_open (t : C) : t \isn't Num.nneg -> 
  exists2 e, 0 < e & forall s, `|s - t| < e -> s \isn't Num.nneg.
Proof.
rewrite Num.Theory.nnegrE lecE/= negb_and -Num.Theory.real_ltNge 
  ?Num.Theory.real0// ?Num.Theory.num_real// =>/orP[P1|P1].
exists (`|Im t|)%:C=>[|s]; first by rewrite ltcR Num.Theory.normr_gt0.
2: exists (`|Re t|)%:C=>[|s]; first by move: P1; rewrite ltcR !lt_def 
  Num.Theory.normr_ge0 Num.Theory.normr_eq0 eq_sym=>/andP[->].
all: rewrite Num.Theory.nnegrE lecE negb_and/= -Num.Theory.normr_gt0=>P2.
move: (le_lt_trans (normc_ge_Im _) P2). 2: move: (le_lt_trans (normc_ge_Re _) P2).
all: rewrite ltcR raddfB/= -Num.Theory.normrN opprB =>P3.
move: (le_lt_trans (Num.Theory.ler_sub_dist _ _) P3).
by rewrite Num.Theory.ltr_subl_addl -Num.Theory.ltr_subl_addr addrN=>->.
move/Num.Theory.ltr_distlC_addr: P3. 
by rewrite Num.Theory.ltr0_norm// addrN -Num.Theory.real_ltNge 
  ?real0// ?Num.Theory.num_real// orbC=>->.
Qed.

Lemma cclosed_ge (y:C) : closed [set x : C | y <= x].
Proof.
rewrite (_ : mkset _ = ~` [set x | ~ 0 <= x - y]); last first.
by rewrite predeqE=>x /=; rewrite notK Num.Theory.subr_ge0.
rewrite closedC. move=> x /= /negP /Cnng_open [e egt0 Pe].
exists e. by apply egt0. rewrite ball_normE=>z.
rewrite /ball/=. suff ->: `|x-z|=`|(z-y)-(x-y)| by move=>/Pe/negP.
by rewrite opprB addrA addrNK -Num.Internals.normrN opprB.
Qed.

Lemma cclosed_le (y : C) : closed [set x : C | x <= y].
Proof.
rewrite (_ : mkset _ = ~` [set x | ~ 0 <= y - x]); last first.
by rewrite predeqE=>x /=; rewrite notK Num.Theory.subr_ge0.
rewrite closedC. move=> x /= /negP/Cnng_open [e egt0 Pe].
exists e. by apply egt0. rewrite ball_normE=>z.
rewrite /ball/=. suff ->: `|x-z|=`|(y-z)-(y-x)| by move=>/Pe/negP.
by rewrite opprB [in RHS]addrC addrA addrNK.
Qed.

Lemma cclosed_eq (y : C) : closed [set x : C | x = y].
Proof.
rewrite (_ : mkset _ = [set x | x <= y] `&` [set x | y <= x]).
apply closedI. apply cclosed_le. apply cclosed_ge.
apply/funext=>x /=. rewrite propeqE. split=>[->//|[P1 P2]].
by apply/eqP; rewrite eq_le P1 P2.
Qed.

Lemma clim_ge_near (x : C) (u : C ^nat) : 
  cvg u -> (\forall n \near \oo, x <= u n) -> x <= lim u.
Proof. by move=> /[swap] /(closed_cvg (>= x))P; apply/P/cclosed_ge. Qed.

Lemma clim_le_near (x : C) (u : C ^nat) : 
  cvg u -> (\forall n \near \oo, x >= u n) -> x >= lim u.
Proof. by move=> /[swap] /(closed_cvg (fun y => y <= x))P; apply/P/cclosed_le. Qed.

Lemma lt_clim (u : C ^nat) (x : C) : nondecreasing_seq u -> cvg u -> x < lim u ->
  \forall n \near \oo, x <= u n.
Proof.
move=> ndu cu Ml; have [[n Mun]|/forallNP Mu] := pselect (exists n, x <= u n).
  near=> m; suff : u n <= u m by exact: le_trans.
  by near: m; exists n.+1 => // p q; apply/ndu/ltnW.
have Cn n : comparable x (u n) by apply/(Num.Theory.comparabler_trans 
  (lt_comparable Ml))/ge_comparable/cnondecreasing_cvg_le.
have {}Mu : forall y, x > u y. move=> y. rewrite comparable_ltNge. by apply/negP.
by rewrite comparable_sym.
have : lim u <= x by apply clim_le_near => //; near=> m; apply/ltW/Mu.
by move/(lt_le_trans Ml); rewrite ltxx.
Unshelve. all: by end_near.
Qed.

Lemma gt_clim (u : C ^nat) (x : C) : nonincreasing_seq u -> cvg u -> x > lim u ->
  \forall n \near \oo, x >= u n.
Proof.
rewrite -nondecreasing_opp=>P1 P2.
rewrite -Num.Theory.ltr_opp2 -climN// =>P3.
move: (lt_clim P1 (is_ccvgN P2) P3)=>[N Sn Pn].
exists N=>// n. move: (Pn n). 
by rewrite /= {2}/GRing.opp/= Num.Theory.ler_opp2.
Qed.

Lemma ler_clim_near (u_ v_ : C ^nat) : cvg u_ -> cvg v_ ->
  (\forall n \near \oo, u_ n <= v_ n) -> lim u_ <= lim v_.
Proof.
move=> uv cu cv; rewrite -Num.Theory.subr_ge0 -climB=>[|//|]; last by apply uv.
apply: clim_ge_near; first by apply: is_ccvgB;[| apply uv].
by apply: filterS cv => n; rewrite Num.Theory.subr_ge0.
Qed.

Lemma clim_ge (x : C) (u : C ^nat) : cvg u -> (forall n, x <= u n) -> x <= lim u.
Proof. by move=>P1 P2; apply/clim_ge_near=>//; exists 0%N=>//. Qed.

Lemma clim_le (x : C) (u : C ^nat) : cvg u -> (forall n, u n <= x) -> lim u <= x.
Proof. by move=>P1 P2; apply/clim_le_near=>//; exists 0%N=>//. Qed.

Lemma ler_clim (u_ v_ : C^nat) : cvg u_ -> cvg v_ ->
  (forall n, u_ n <= v_ n) -> lim u_ <= lim v_.
Proof. by move=>P1 P2 P3; apply/ler_clim_near=>//; exists 0%N=>//. Qed.

End complex_monotone.

Section matrix_CompleteNormedModule.
Variables (R: realType) (m n : nat).

Canonical matrix_completeNormedModule :=
  [completeNormedModType R of 'M[R]_(m.+1, n.+1)].

End matrix_CompleteNormedModule.

Module VNorm.

Section Definitions.
Variables (R: numDomainType) (T : lmodType R).

Structure vnorm := Vnorm {
  operator : T -> R;
  _ : forall x y, operator (x + y) <= operator x + operator y;
  _ : forall x, operator x = 0 -> x = 0;
  _ : forall a x, operator (a *: x) = `|a| * operator x;
}.
Local Coercion operator : vnorm >-> Funclass.

Let op_id (op1 op2 : T -> R) := phant_id op1 op2.

Definition clone_vnorm op :=
  fun (opL : vnorm) & op_id opL op =>
  fun optr op0 opz (opL' := @Vnorm op optr op0 opz)
    & phant_id opL' opL => opL'.

End Definitions.

Module Import Exports.
Coercion operator : vnorm >-> Funclass.
Notation vnorm := vnorm.
Notation Vnorm := Vnorm.
Notation "[ 'vnorm' 'of' f ]" := (@clone_vnorm _ _ f _ id _ _ _ id)
  (at level 0, format"[ 'vnorm'  'of'  f ]") : form_scope.
End Exports.

End VNorm.
Import VNorm.Exports.

Section VNormTheory.
Import Num.Def Num.Theory.
Variable (R: numDomainType) (V: lmodType R) (mnorm : vnorm V).
Local Notation "`[ x ]" := (mnorm x).

Lemma lev_norm_add x y : (`[ x + y ]) <= (`[ x ] + `[ y ]).
Proof. by case: mnorm x y. Qed.

Lemma normv0_eq0 x: `[ x ] = 0 -> x = 0.
Proof. by case: mnorm x. Qed.

Lemma normvZ a x: `[ a *: x ] = `|a| * `[ x ].
Proof. by case: mnorm a x. Qed.

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
move=>x; move: (lev_norm_add x (-x)).
by rewrite addrN normvN -mulr2n normv0 pmulrn_lge0.
Qed.

Lemma normv_nneg A : `[ A ] \is Num.nneg.
Proof. by rewrite qualifE normv_ge0. Qed.

Lemma normv_real x : `[ x ] \is Num.real.
Proof. apply/ger0_real/normv_ge0. Qed.

Lemma normv_gt0 x : `[ x ] > 0 = (x != 0).
Proof. by rewrite lt_def normv_ge0 andbT normv_eq0. Qed.

Lemma lev_norm_sub v w : `[v - w] <= `[v] + `[w].
Proof. by rewrite (le_trans (lev_norm_add _ _)) ?normvN. Qed.

Lemma lev_dist_add u v w : `[v-w] <= `[v-u] + `[u-w].
Proof. by rewrite (le_trans _ (lev_norm_add _ _)) // addrA addrNK. Qed.

Lemma lev_sub_norm_add v w : `[v] - `[w] <= `[v+w].
Proof.
rewrite -{1}[v](addrK w) lter_sub_addl.
by rewrite (le_trans (lev_norm_add _ _)) // addrC normvN.
Qed.

Lemma lev_sub_dist v w : `[v] - `[w] <= `[v-w].
Proof. by rewrite -[`[w]]normvN lev_sub_norm_add. Qed.

Lemma lev_dist_dist v w : `| `[v] - `[w] | <= `[v-w].
Proof.
have [ | | _ | _ ] // := @real_leP _ (mnorm v) (mnorm w); last by rewrite lev_sub_dist.
1,2: by rewrite realE normv_ge0. by rewrite -(normvN (v-w)) opprB lev_sub_dist.
Qed.

Lemma normv_sum (I: finType) (r : seq I) (P: pred I) f :
  mnorm (\sum_(i <- r | P i) f i) <= \sum_(i <- r | P i) mnorm (f i).
Proof.
elim: r => [|x r IH]; first by rewrite !big_nil normv0.
rewrite !big_cons. case: (P x)=>//.
apply (le_trans (lev_norm_add _ _)). by apply ler_add.
Qed.

Definition cauchy_seqv  (u: nat -> V) := 
  forall e : R, 0 < e -> exists N : nat, 
    forall s t, (N <= s)%N -> (N <= t)%N -> mnorm (u s - u t) < e.

Lemma cauchy_seqv_cst x : cauchy_seqv (fun=>x).
by move=>e egt0; exists 0%N=> s t _ _; rewrite subrr normv0. Qed.

End VNormTheory.

(* vorder is regarded as operator rather than a type *)
(* so we can use different vorder of the same type   *)

Fact vorder_display : unit. Proof. by []. Qed.
Notation "x '⊑' y" := (@Order.le vorder_display _ x y) (at level 70, y at next level).
Notation "x '⊏' y" := (@Order.lt vorder_display _ x y) (at level 70, y at next level).
Notation "x '⊑' y '⊑' z" := ((x ⊑ y) && (y ⊑ z)) (at level 70, y at next level).
Notation "'ubounded_by' b f" := (forall i, f i ⊑ b) (at level 10, b, f at next level).
Notation "'lbounded_by' b f" := (forall i, b ⊑ f i) (at level 10, b, f at next level).
Notation "'nondecreasing_seq' f" := ({homo f : n m / (n <= m)%nat >-> (n <= m)%O})
  (at level 10).
Notation "'nonincreasing_seq' f" := ({homo f : n m / (n <= m)%nat >-> (n >= m)%O})
  (at level 10).
Notation "'increasing_seq' f" := ({mono f : n m / (n <= m)%nat >-> (n <= m)%O})
  (at level 10).
Notation "'decreasing_seq' f" := ({mono f : n m / (n <= m)%nat >-> (n >= m)%O})
  (at level 10).

Module VOrder.

Record mixin_of (R: numFieldType) (T: lmodType R)
       (Rorder : Order.POrder.mixin_of (Equality.class T))
       (le_op := Order.POrder.le Rorder) (lt_op := Order.POrder.lt Rorder)
  := Mixin {
  _  : forall (z x y : T), le_op x y -> le_op (x + z) (y + z);
  _  : forall (e : R) (x y : T), 0 < e -> le_op x y -> le_op (e *: x) (e *: y);
}.

Section ClassDef.
Variable (R: numFieldType).
Set Primitive Projections.
Record class_of T := Class {
  base : GRing.Lmodule.class_of R T;
  order_mixin : Order.POrder.mixin_of (Equality.class (GRing.Lmodule.Pack _ base));
  mixin : mixin_of order_mixin;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> GRing.Lmodule.class_of.
Local Coercion order_base T (class_of_T : class_of T) :=
  @Order.POrder.Class _ class_of_T (order_mixin class_of_T).

Structure type (phR : phant R) := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (phR : phant R) (T : Type) (cT : type phR).
Definition class := let: Pack _ c  as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack phR T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack (b0 : GRing.Lmodule.class_of R T) om0
           (m0 : @mixin_of R (GRing.Lmodule.Pack _ b0) om0) := 
  fun bT (b : GRing.Lmodule.class_of R T)
      & phant_id (@GRing.Lmodule.class R (Phant R) bT) b =>
  fun om & phant_id om0 om =>
  fun m & phant_id m0 m =>
  @Pack phR T (@Class T b om m).

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition zmodType := @GRing.Zmodule.Pack cT xclass.
Definition lmodType := @GRing.Lmodule.Pack R phR cT xclass.
Definition porderType := @Order.POrder.Pack vorder_display cT xclass.
Definition porder_zmodType := @GRing.Zmodule.Pack porderType xclass.
Definition porder_lmodType := @GRing.Lmodule.Pack R phR porderType xclass.

End ClassDef.

Module Exports.
Coercion sort : type >-> Sortclass.
Coercion base  : class_of >-> GRing.Lmodule.class_of.
Coercion order_base : class_of >-> Order.POrder.class_of.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion lmodType : type >-> GRing.Lmodule.type.
Canonical lmodType.
Coercion porderType : type >-> Order.POrder.type.
Canonical porderType.
Canonical porder_zmodType.
Canonical porder_lmodType.
Notation vorderType R := (type (Phant R)).
Notation VOrderType R T m := (@pack _ (Phant R) T _ _ m _   _ id _ id _ id).
Notation VOrderMixin := Mixin.
Notation "[ 'vorderType' R 'of' T 'for' cT ]" := (@clone _ (Phant R) T cT _ idfun)
  (at level 0, format "[ 'vorderType'  R  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'vorderType' R 'of' T ]" := (@clone _ (Phant R) T _ _ id)
  (at level 0, format "[ 'vorderType'  R  'of'  T ]") : form_scope.
End Exports.

End VOrder.
Import VOrder.Exports.

Module CanVOrder.

Record mixin_of (R: numFieldType) (T: vorderType R)
  := Mixin {
  _  : forall (x : T) (e : R), (0 : T) ⊏ x -> (0 : T) ⊑ (e *: x) = (0 <= e);
}.

Section ClassDef.
Variable (R: numFieldType).
Set Primitive Projections.
Record class_of T := Class {
  base : VOrder.class_of R T;
  mixin : mixin_of (VOrder.Pack _ base);
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> VOrder.class_of.

Structure type (phR : phant R) := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (phR : phant R) (T : Type) (cT : type phR).
Definition class := let: Pack _ c  as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack phR T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack b0 (m0 : mixin_of (@VOrder.Pack _ (Phant R) T b0)) :=
  fun bT b & phant_id (@VOrder.class _ (Phant R) bT) b =>
  fun    m & phant_id m0 m => Pack phR (@Class T b m).

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition zmodType := @GRing.Zmodule.Pack cT xclass.
Definition lmodType := @GRing.Lmodule.Pack R phR cT xclass.
Definition porderType := @Order.POrder.Pack vorder_display cT xclass.
Definition porder_zmodType := @GRing.Zmodule.Pack porderType xclass.
Definition porder_lmodType := @GRing.Lmodule.Pack R phR porderType xclass.
Definition vorderType := @VOrder.Pack R phR cT xclass.

End ClassDef.

Module Exports.
Coercion sort : type >-> Sortclass.
Coercion base  : class_of >-> VOrder.class_of.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion lmodType : type >-> GRing.Lmodule.type.
Canonical lmodType.
Coercion porderType : type >-> Order.POrder.type.
Canonical porderType.
Canonical porder_zmodType.
Canonical porder_lmodType.
Coercion vorderType : type >-> VOrder.type.
Canonical vorderType.
Notation canVOrderType R := (type (Phant R)).
Notation CanVOrderType R T m := (@pack _ (Phant R) T _ m _ _ id _ id).
Notation CanVOrderMixin := Mixin.
Notation "[ 'canVOrderType' R 'of' T 'for' cT ]" := (@clone _ (Phant R) T cT _ idfun)
  (at level 0, format "[ 'canVOrderType'  R  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'canVOrderType' R 'of' T ]" := (@clone _ (Phant R) T _ _ id)
  (at level 0, format "[ 'canVOrderType'  R  'of'  T ]") : form_scope.
End Exports.

End CanVOrder.
Import CanVOrder.Exports.

Lemma scalerNN (R : ringType) (V : lmodType R) (a : R) (x : V) : 
  (- a) *: (- x) = a *: x.
Proof. by rewrite scalerN scaleNr opprK. Qed.

Section VOrderTheory.
Variable (R: numFieldType) (T : vorderType R).
Implicit Type (x y z : T) (a b c : R).
Local Notation "'0" := (0 : T).

Lemma lev_add2rP z x y : x ⊑ y -> x + z ⊑ y + z.
Proof. by move: x y z; case: T=>?[??[P?]] x y z; apply P. Qed.
Lemma lev_pscale2lP (e : R) x y : 0 < e -> x ⊑ y -> (e *: x) ⊑ (e *: y).
Proof. by move: e x y; case: T=>?[??[? P]] e x y; apply P. Qed.

Lemma subv_ge0 x y : ('0 ⊑ x - y) = (y ⊑ x).
Proof. 
apply/Bool.eq_iff_eq_true; split=>[/(@lev_add2rP y)|/(@lev_add2rP (-y))];
by rewrite ?addrNK ?add0r// addrN.
Qed.

Lemma subv_gt0 x y : ('0 ⊏ y - x) = (x ⊏ y).
Proof. by rewrite !lt_def subr_eq0 subv_ge0. Qed.
Lemma subv_le0  x y : (y - x ⊑ 0) = (y ⊑ x).
Proof. by rewrite -subv_ge0 opprB add0r subv_ge0. Qed.
Lemma subv_lt0  x y : (y - x ⊏ 0) = (y ⊏ x).
Proof. by rewrite -subv_gt0 opprB add0r subv_gt0. Qed.

Definition subv_lte0 := (subv_le0, subv_lt0).
Definition subv_gte0 := (subv_ge0, subv_gt0).
Definition subv_cp0 := (subv_lte0, subv_gte0).

Lemma lev_opp2 : {mono (-%R : T -> T) : x y /~ x ⊑ y }.
Proof. by move=>x y; rewrite -subv_ge0 opprK addrC subv_ge0. Qed.
Hint Resolve lev_opp2 : core.

Lemma ltv_opp2 : {mono (-%R : T -> T) : x y /~ x ⊏ y }.
Proof. by move=> x y /=; rewrite leW_nmono. Qed.
Hint Resolve ltv_opp2 : core.
Definition ltev_opp2 := (lev_opp2, ltv_opp2).

Lemma addv_ge0 x y : '0 ⊑ x -> '0 ⊑ y -> '0 ⊑ x + y.
Proof.
by move=>P1 P2; apply: (le_trans P1); rewrite -subv_ge0 addrC addrA addNr add0r.
Qed.

Lemma addv_gt0 x y : '0 ⊏ x -> '0 ⊏ y -> '0 ⊏ x + y.
Proof.
rewrite !lt_def=>/andP[/negPf Pf Pf1]/andP[Pg Pg1]; rewrite (addv_ge0 Pf1 Pg1) andbT.
case: eqP=>//= P1; move: Pg1; rewrite -P1 -subv_ge0 opprD addrC addrNK -oppr0 lev_opp2=>P2.
by rewrite -Pf eq_le Pf1 P2.
Qed.

Lemma le0v x : ('0 ⊑ x) = (x == 0) || ('0 ⊏ x).
Proof. by rewrite lt_def; case: eqP => // ->; rewrite lexx. Qed.

Lemma lev_add2r x : {mono +%R^~ x : y z / y ⊑ z}.
Proof. by move=>y z; rewrite -subv_ge0 opprD addrACA addrN addr0 subv_ge0. Qed.

Lemma lev_oppr x y : (x ⊑ - y) = (y ⊑ - x).
Proof. by rewrite (monoRL opprK lev_opp2). Qed.

Lemma ltv_oppr x y : (x ⊏ - y) = (y ⊏ - x).
Proof. by rewrite (monoRL opprK (leW_nmono lev_opp2)). Qed.

Definition ltev_oppr := (lev_oppr, ltv_oppr).

Lemma lev_oppl x y : (- x ⊑ y) = (- y ⊑ x).
Proof. by rewrite (monoLR opprK lev_opp2). Qed.

Lemma ltv_oppl x y : (- x ⊏ y) = (- y ⊏ x).
Proof. by rewrite (monoLR opprK (leW_nmono lev_opp2)). Qed.

Definition ltev_oppl := (lev_oppl, ltv_oppl).

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
Definition ltev_oppE := (oppv_cp0, ltev_opp2).

Lemma gev0_cp x : '0 ⊑ x -> (- x ⊑ 0) * (- x ⊑ x).
Proof. by move=> hx; rewrite oppv_cp0 hx (@le_trans _ _ '0) ?oppv_cp0. Qed.

Lemma gtv0_cp x : '0 ⊏ x ->
  ('0 ⊑ x) * (- x ⊑ 0) * (- x ⊑ x) * (- x ⊏ 0) * (- x ⊏ x).
Proof.
move=> hx; move: (ltW hx) => hx'; rewrite !gev0_cp hx'=>[|//|//].
by rewrite oppv_cp0 hx (@lt_trans _ _ '0) ?oppv_cp0.
Qed.

Lemma lev0_cp x : x ⊑ 0 -> ('0 ⊑ - x) * (x ⊑ - x).
Proof. by move=> hx; rewrite oppv_cp0 hx (@le_trans _ _ '0) ?oppv_cp0. Qed.

Lemma ltv0_cp x :
  x ⊏ 0 -> (x ⊑ 0) * ('0 ⊑ - x) * (x ⊑ - x) * ('0 ⊏ - x) * (x ⊏ - x).
Proof.
move=> hx; move: (ltW hx) => hx'; rewrite !lev0_cp hx' =>[|//|//].
by rewrite oppv_cp0 hx (@lt_trans _ _ '0) ?oppv_cp0.
Qed.

(* Monotony of addition *)
Lemma lev_add2l x : {mono +%R x : y z / y ⊑ z}.
Proof. by move=>y z; rewrite ![x + _]addrC lev_add2r. Qed.

Lemma ltv_add2l x : {mono +%R x : y z / y ⊏ z}.
Proof. by move=> y z /=; rewrite (leW_mono (lev_add2l _)). Qed.

Lemma ltv_add2r x : {mono +%R^~ x : y z / y ⊏ z}.
Proof. by move=> y z /=; rewrite (leW_mono (lev_add2r _)). Qed.

Definition lev_add2 := (lev_add2l, lev_add2r).
Definition ltv_add2 := (ltv_add2l, ltv_add2r).
Definition ltev_add2 := (lev_add2, ltv_add2).

(* Addition, subtraction and transitivity *)
Lemma lev_add x y z t : x ⊑ y -> z ⊑ t -> x + z ⊑ y + t.
Proof. by move=> lxy lzt; rewrite (@le_trans _ _ (y + z)) ?ltev_add2. Qed.

Lemma lev_lt_add x y z t : x ⊑ y -> z ⊏ t -> x + z ⊏ y + t.
Proof. by move=> lxy lzt; rewrite (@le_lt_trans _ _ (y + z)) ?ltev_add2. Qed.

Lemma ltv_le_add x y z t : x ⊏ y -> z ⊑ t -> x + z ⊏ y + t.
Proof. by move=> lxy lzt; rewrite (@lt_le_trans _ _ (y + z)) ?ltev_add2. Qed.

Lemma ltv_add x y z t : x ⊏ y -> z ⊏ t -> x + z ⊏ y + t.
Proof. by move=> lxy lzt; rewrite ltv_le_add ?ltW. Qed.

Lemma lev_sub x y z t : x ⊑ y -> t ⊑ z -> x - z ⊑ y - t.
Proof. by move=> lxy ltz; rewrite lev_add ?ltev_opp2. Qed.

Lemma lev_lt_sub x y z t : x ⊑ y -> t ⊏ z -> x - z ⊏ y - t.
Proof. by move=> lxy lzt; rewrite lev_lt_add ?ltev_opp2. Qed.

Lemma ltv_le_sub x y z t : x ⊏ y -> t ⊑ z -> x - z ⊏ y - t.
Proof. by move=> lxy lzt; rewrite ltv_le_add ?ltev_opp2. Qed.

Lemma ltv_sub x y z t : x ⊏ y -> t ⊏ z -> x - z ⊏ y - t.
Proof. by move=> lxy lzt; rewrite ltv_add ?ltev_opp2. Qed.

Lemma lev_subl_addr x y z : (x - y ⊑ z) = (x ⊑ z + y).
Proof. by rewrite (monoLR (addrK _) (lev_add2r _)). Qed.

Lemma ltv_subl_addr x y z : (x - y ⊏ z) = (x ⊏ z + y).
Proof. by rewrite (monoLR (addrK _) (ltv_add2r _)). Qed.

Lemma lev_subr_addr x y z : (x ⊑ y - z) = (x + z ⊑ y).
Proof. by rewrite (monoLR (addrNK _) (lev_add2r _)). Qed.

Lemma ltv_subr_addr x y z : (x ⊏ y - z) = (x + z ⊏ y).
Proof. by rewrite (monoLR (addrNK _) (ltv_add2r _)). Qed.

Definition lev_sub_addr := (lev_subl_addr, lev_subr_addr).
Definition ltv_sub_addr := (ltv_subl_addr, ltv_subr_addr).
Definition ltev_sub_addr := (lev_sub_addr, ltv_sub_addr).

Lemma lev_subl_addl x y z : (x - y ⊑ z) = (x ⊑ y + z).
Proof. by rewrite ltev_sub_addr addrC. Qed.

Lemma ltv_subl_addl x y z : (x - y ⊏ z) = (x ⊏ y + z).
Proof. by rewrite ltev_sub_addr addrC. Qed.

Lemma lev_subr_addl x y z : (x ⊑ y - z) = (z + x ⊑ y).
Proof. by rewrite ltev_sub_addr addrC. Qed.

Lemma ltv_subr_addl x y z : (x ⊏ y - z) = (z + x ⊏ y).
Proof. by rewrite ltev_sub_addr addrC. Qed.

Definition lev_sub_addl := (lev_subl_addl, lev_subr_addl).
Definition ltv_sub_addl := (ltv_subl_addl, ltv_subr_addl).
Definition ltev_sub_addl := (lev_sub_addl, ltv_sub_addl).

Lemma lev_addl x y : (x ⊑ x + y) = ('0 ⊑ y).
Proof. by rewrite -{1}[x]addr0 ltev_add2. Qed.

Lemma ltv_addl x y : (x ⊏ x + y) = ('0 ⊏ y).
Proof. by rewrite -{1}[x]addr0 ltev_add2. Qed.

Lemma lev_addr x y : (x ⊑ y + x) = ('0 ⊑ y).
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

Definition cpv_add := (lev_addl, lev_addr, gev_addl, gev_addl,
                       ltv_addl, ltv_addr, gtv_addl, gtv_addl).

(* Addition with levt member knwon to be positive/negative *)
Lemma lev_paddl y x z : '0 ⊑ x -> y ⊑ z -> y ⊑ x + z.
Proof. by move=> *; rewrite -[y]add0r lev_add. Qed.

Lemma ltv_paddl y x z : '0 ⊑ x -> y ⊏ z -> y ⊏ x + z.
Proof. by move=> *; rewrite -[y]add0r lev_lt_add. Qed.

Lemma ltv_spaddl y x z : '0 ⊏ x -> y ⊑ z -> y ⊏ x + z.
Proof. by move=> *; rewrite -[y]add0r ltv_le_add. Qed.

Lemma ltv_spsaddl y x z : '0 ⊏ x -> y ⊏ z -> y ⊏ x + z.
Proof. by move=> *; rewrite -[y]add0r ltv_add. Qed.

Lemma lev_naddl y x z : x ⊑ 0 -> y ⊑ z -> x + y ⊑ z.
Proof. by move=> *; rewrite -[z]add0r lev_add. Qed.

Lemma ltv_naddl y x z : x ⊑ 0 -> y ⊏ z -> x + y ⊏ z.
Proof. by move=> *; rewrite -[z]add0r lev_lt_add. Qed.

Lemma ltv_snaddl y x z : x ⊏ 0 -> y ⊑ z -> x + y ⊏ z.
Proof. by move=> *; rewrite -[z]add0r ltv_le_add. Qed.

Lemma ltv_snsaddl y x z : x ⊏ 0 -> y ⊏ z -> x + y ⊏ z.
Proof. by move=> *; rewrite -[z]add0r ltv_add. Qed.

(* Addition with right member we know positive/negative *)
Lemma lev_paddr y x z : '0 ⊑ x -> y ⊑ z -> y ⊑ z + x.
Proof. by move=> *; rewrite [_ + x]addrC lev_paddl. Qed.

Lemma ltv_paddr y x z : '0 ⊑ x -> y ⊏ z -> y ⊏ z + x.
Proof. by move=> *; rewrite [_ + x]addrC ltv_paddl. Qed.

Lemma ltv_spaddr y x z : '0 ⊏ x -> y ⊑ z -> y ⊏ z + x.
Proof. by move=> *; rewrite [_ + x]addrC ltv_spaddl. Qed.

Lemma ltv_spsaddr y x z : '0 ⊏ x -> y ⊏ z -> y ⊏ z + x.
Proof. by move=> *; rewrite [_ + x]addrC ltv_spsaddl. Qed.

Lemma lev_naddr y x z : x ⊑ 0 -> y ⊑ z -> y + x ⊑ z.
Proof. by move=> *; rewrite [_ + x]addrC lev_naddl. Qed.

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
Proof. exact: (big_ind2 _ (lexx _) lev_add). Qed.

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
move=> F_ge0 /eqP; rewrite psumv_eq0=>[|//].
rewrite -big_all big_andE => /forallP hF i Pi.
by move: (hF i); rewrite implyTb Pi /= => /eqP.
Qed.

Lemma lt0v x : ('0 ⊏ x) = (x != 0) && ('0 ⊑ x). Proof. by rewrite lt_def. Qed.

Lemma lt0v_neq0 x : '0 ⊏ x -> x != 0.
Proof. by rewrite lt0v; case/andP. Qed.

Lemma ltv0_neq0 x : x ⊏ 0 -> x != 0.
Proof. by rewrite lt_neqAle; case/andP. Qed.

Import Num.Theory.

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
by move=> x_lt0 y z /=; rewrite -lev_opp2 -!scaleNr lev_pscale2l ?oppr_gt0.
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
by move=> x_le0 y z leyz; rewrite -![a *: _]scalerNN lev_wpscale2l ?ltev_oppE// lter_oppE.
Qed.

Lemma lev_wnscale2r x : x ⊑ 0 -> {homo *:%R^~ x : y z /~ (y <= z)%O}.
Proof.
by move=> x_le0 y z leyz; rewrite -![_ *: x]scalerNN lev_wpscale2r ?ltev_oppE// lter_oppE.
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

Lemma lev_wmuln2r n : {homo natmul^~ n : x y / x ⊑ y}.
Proof. by move=> x y hxy /=; case: n=> // n; rewrite lev_pmuln2r. Qed.

Lemma mulvn_wge0 x n : '0 ⊑ x -> '0 ⊑ x *+ n.
Proof. by move=> /(lev_wmuln2r n); rewrite mul0rn. Qed.

Lemma mulvn_wle0 x n : x ⊑ 0 -> x *+ n ⊑ 0.
Proof. by move=> /(lev_wmuln2r n); rewrite mul0rn. Qed.

Lemma lev_muln2r n x y : (x *+ n ⊑ y *+ n) = ((n == 0%N) || (x ⊑ y)).
Proof. by case: n => [|n]; rewrite ?lexx ?eqxx // lev_pmuln2r. Qed.

Lemma ltv_muln2r n x y : (x *+ n ⊏ y *+ n) = ((0 < n)%N && (x ⊏ y)).
Proof. by case: n => [|n]; rewrite ?lexx ?eqxx // ltv_pmuln2r. Qed.

Lemma eqv_muln2r n x y : (x *+ n == y *+ n) = (n == 0)%N || (x == y).
Proof. by rewrite {1}eq_le [x == _]eq_le !lev_muln2r -orb_andr. Qed.

(* More characteristic zero properties. *)

Lemma mulvn_eq0 x n : (x *+ n == 0) = ((n == 0)%N || (x == 0)).
Proof. by rewrite -{1}(mul0rn [zmodType of T] n) eqv_muln2r. Qed.

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
by move=> xle0 m n hmn /=; rewrite -lev_opp2 -!mulNrn lev_wpmuln2l // oppv_cp0.
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
by move=> x_lt0 m n /=; rewrite -lev_opp2 -!mulNrn lev_pmuln2l // oppv_gt0.
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
Proof. by move=> x_lt0; rewrite -scalerNN pscalev_rgt0 ?ltev_oppE// lter_oppE. Qed.

Lemma nscalev_rge0 a y : a < 0 -> ('0 ⊑ a *: y) = (y ⊑ 0).
Proof. by move=> x_lt0; rewrite -scalerNN pscalev_rge0 ?ltev_oppE// lter_oppE. Qed.

Lemma nscalev_rlt0 a y : a < 0 -> (a *: y ⊏ 0) = ('0 ⊏ y).
Proof. by move=> x_lt0; rewrite -scalerNN pscalev_rlt0 ?ltev_oppE// lter_oppE. Qed.

Lemma nscalev_rle0 a y : a < 0 -> (a *: y ⊑ 0) = ('0 ⊑ y).
Proof. by move=> x_lt0; rewrite -scalerNN pscalev_rle0 ?ltev_oppE// lter_oppE. Qed.

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

End VOrderTheory.

Section CanVOrderTheory.
Variable (R: numFieldType) (T : canVOrderType R).
Implicit Type (x y z : T) (a b c : R).
Local Notation "'0" := (0 : T).

Lemma pscalev_lge0 x a : '0 ⊏ x -> '0 ⊑ a *: x = (0 <= a).
Proof. by move: x a; case: T=>?[?[P]] x a; apply P. Qed.

Lemma pscalev_lgt0 y a : '0 ⊏ y -> ('0 ⊏ a *: y) = (0 < a).
Proof.
by move=>Py; rewrite !lt_def scaler_eq0 negb_or pscalev_lge0// lt0v_neq0// andbT.
Qed.

Import Num.Theory.

Lemma lev_pscale2r x : '0 ⊏ x -> {mono *:%R^~ x : x y / (x <= y)%O}.
Proof.
by move=>Px a b; rewrite -subv_ge0 -scalerBl pscalev_lge0// subr_ge0.
Qed.  

Lemma ltv_pscale2r x : '0 ⊏ x -> {mono *:%R^~ x : x y / (x < y)%O}.
Proof. by move=> x_gt0; apply: leW_mono (lev_pscale2r _). Qed.

Definition ltev_pscale2r := (lev_pscale2r, ltv_pscale2r).


Lemma lev_nscale2r x : x ⊏ 0 -> {mono *:%R^~ x : x y /~ (x <= y)%O}.
Proof.
by move=> x_lt0 y z /=; rewrite -lev_opp2 -!scalerN lev_pscale2r// oppv_gt0.
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
Proof. by move=> x_lt0; rewrite -scalerNN pscalev_lgt0 ?ltev_oppE// lter_oppE. Qed.

Lemma nscalev_lge0 x a : x ⊏ 0 -> ('0 ⊑ a *: x) = (a <= 0).
Proof. by move=> x_lt0; rewrite -scalerNN pscalev_lge0 ?ltev_oppE// lter_oppE. Qed.

Lemma nscalev_llt0 x a : x ⊏ 0 -> (a *: x ⊏ 0) = (0 < a).
Proof. by move=> x_lt0; rewrite -scalerNN pscalev_llt0 ?ltev_oppE// lter_oppE. Qed.

Lemma nscalev_lle0 x a : x ⊏ 0 -> (a *: x ⊑ 0) = (0 <= a).
Proof. by move=> x_lt0; rewrite -scalerNN pscalev_lle0 ?ltev_oppE// lter_oppE. Qed.

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

Module BRegVOrder.

Section ClassDef.
Variable (R: numFieldType) (U V W : vorderType R).
Implicit Type phUVW : phant (U -> V -> W).

Record mixin_of (op : U -> V -> W) := Mixin {
  _ : forall x y, op x y == 0 = (x == 0) || (y == 0);
  _ : forall x y, (0 : U) ⊏ x -> ((0 : W) ⊑ op x y) = ((0 : V) ⊑ y);
  _ : forall y x, (0 : V) ⊏ y -> ((0 : W) ⊑ op x y) = ((0 : U) ⊑ x);
}.

Record class_of f : Prop := Class {
  basel : forall u', GRing.Additive.axiom (f^~ u');
  baser : forall u, GRing.Additive.axiom (f u);
  mixin : mixin_of f
}.

Structure map phUVW := Pack {apply; _ : class_of apply}.
Local Coercion apply : map >-> Funclass.

Definition class phUVW (cF : map phUVW) := 
    let: Pack _ c as cF' := cF return class_of cF' in c.
Definition clone phUVW (f g : U -> V -> W) (cF : map phUVW) 
  fL of phant_id g (apply cF) & phant_id fL class := @Pack phUVW f fL.

Definition pack (phUW : phant (U -> W)) (phVW : phant (V -> W))
           (revf : V -> U -> W) (rf : revop revf) f (g : U -> V -> W) m0 of (g = fun_of_revop rf) :=
  fun (bFl : V -> GRing.Additive.map phUW) flc of (forall v, revf v = bFl v) &
      (forall v, phant_id (GRing.Additive.class (bFl v)) (flc v)) =>
  fun (bFr : U -> GRing.Additive.map phVW) frc of (forall u, g u = bFr u) &
      (forall u, phant_id (GRing.Additive.class (bFr u)) (frc u)) =>
  @Pack (Phant _) f (Class flc frc m0).

Definition additiver phVW phUVW (u : U) cF := GRing.Additive.Pack phVW 
  (baser (@class phUVW cF) u).
Definition additivel phUW phUVW (v : V) (cF : map phUVW) :=
  @GRing.Additive.Pack _ _ phUW (applyar cF v) (basel (@class phUVW cF) v).

End ClassDef.

Module Exports.
Coercion baser : class_of >-> Funclass.
Coercion apply : map >-> Funclass.
Notation bregVOrderMixin := Mixin.
Notation bregVOrderType f M := (@pack _ _ _ _ _ _ _ _ f f M erefl _ _ 
(fun=> erefl) (fun=> idfun) _ _ (fun=> erefl) (fun=> idfun)).
Notation "{ 'bregVOrder' fUV }" := (map (Phant fUV))
  (at level 0, format "{ 'bregVOrder'  fUV }") : ring_scope.
Notation "[ 'bregVOrder' 'of' f 'as' g ]" := (@clone _ _ _ _ _ f g _ _ idfun id)
  (at level 0, format "[ 'bregVOrder'  'of'  f  'as'  g ]") : form_scope.
Notation "[ 'bregVOrder' 'of' f ]" := (@clone _ _ _ _ _ f f _ _ id id)
  (at level 0, format "[ 'bregVOrder'  'of'  f ]") : form_scope.
Canonical additiver.
Canonical additivel.
End Exports.

End BRegVOrder.
Export BRegVOrder.Exports.

Section BRegVOrderTheory.
Variable (R: numFieldType) (U V W : vorderType R) (f : {bregVOrder U -> V -> W}).
Implicit Type (a b c : U) (x y z : V).

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

Lemma bregv_eq0 a x : f a x == 0 = (a == 0) || (x == 0).
Proof. by move: a x; case: f=>/=?[??[???]]. Qed.

Lemma pbregv_rge0 a x : l0 ⊏ a -> (b0 ⊑ f a x) = (r0 ⊑ x).
Proof. move: a x; case: f=>/=?[??[? P?]]; apply P. Qed.

Lemma pbregv_lge0 x a : r0 ⊏ x -> (b0 ⊑ f a x) = (l0 ⊑ a).
Proof. move: x a; case: f=>/=?[??[?? P]]; apply P. Qed.

Lemma pbregv_rgt0 a x : l0 ⊏ a -> (b0 ⊏ f a x) = (r0 ⊏ x).
Proof.
move=>xgt0. rewrite !lt0v (pbregv_rge0 _ xgt0) bregv_eq0//.
by move: xgt0; rewrite lt_def=>/andP[/negPf->].
Qed.

Lemma pbregv_lgt0 x a : r0 ⊏ x -> (b0 ⊏ f a x) = (l0 ⊏ a).
Proof.
move=>xgt0. rewrite !lt0v (pbregv_lge0 _ xgt0) bregv_eq0//.
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
by move=> x_lt0 y z /=; rewrite -lev_opp2 -!bregvNl/= lev_pbreg2l ?oppv_gt0.
Qed.

Lemma ltv_nbreg2l a : a ⊏ 0 -> {mono (f a) : x y /~ x ⊏ y}.
Proof. by move=> x_lt0; apply: leW_nmono (lev_nbreg2l _). Qed.

Definition ltev_nbreg2l := (lev_nbreg2l, ltv_nbreg2l).

Lemma lev_nbreg2r x : x ⊏ 0 -> {mono f^~ x : x y /~ x ⊑ y}.
Proof.
by move=> x_lt0 y z /=; rewrite -lev_opp2 -!bregvNr lev_pbreg2r// oppv_gt0.
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
by move=> x_le0 y z leyz; rewrite -![f a _]bregvNN lev_wpbreg2l ?ltev_oppE.
Qed.

Lemma lev_wpbreg2r x : r0 ⊑ x -> {homo f^~ x : y z / y ⊑ z}.
Proof.
by rewrite le0v => /orP[/eqP-> y z | /lev_pbreg2r/mono2W//]; rewrite !bregv0r.
Qed.

Lemma lev_wnbreg2r x : x ⊑ 0 -> {homo f^~ x : y z /~ y ⊑ z}.
Proof.
by move=> x_le0 y z leyz; rewrite -![f _ x]bregvNN lev_wpbreg2r ?ltev_oppE.
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
Proof. by move=> x_lt0; rewrite -bregvNN pbregv_rgt0 ?ltev_oppE. Qed.

Lemma nbregv_rge0 a x : a ⊏ 0 -> (b0 ⊑ f a x) = (x ⊑ 0).
Proof. by move=> x_lt0; rewrite -bregvNN pbregv_rge0 ?ltev_oppE. Qed.

Lemma nbregv_rlt0 a x : a ⊏ 0 -> (f a x ⊏ 0) = (r0 ⊏ x).
Proof. by move=> x_lt0; rewrite -bregvNN pbregv_rlt0 ?ltev_oppE. Qed.

Lemma nbregv_rle0 a x : a ⊏ 0 -> (f a x ⊑ 0) = (r0 ⊑ x).
Proof. by move=> x_lt0; rewrite -bregvNN pbregv_rle0 ?ltev_oppE. Qed.

Lemma pbregv_llt0 x a : r0 ⊏ x -> (f a x ⊏ 0) = (a ⊏ 0).
Proof. by move=> x_gt0; rewrite -!oppv_gt0 -bregvNl pbregv_lgt0// oppv_gt0. Qed.

Lemma pbregv_lle0 x a : r0 ⊏ x -> (f a x ⊑ 0) = (a ⊑ 0).
Proof. by move=> x_gt0; rewrite -!oppv_ge0 -bregvNl pbregv_lge0// oppr_ge0. Qed.

Lemma nbregv_lgt0 x a : x ⊏ 0 -> (b0 ⊏ f a x) = (a ⊏ 0).
Proof. by move=> x_lt0; rewrite -bregvNN pbregv_lgt0 ?ltev_oppE. Qed.

Lemma nbregv_lge0 x a : x ⊏ 0 -> (b0 ⊑ f a x) = (a ⊑ 0).
Proof. by move=> x_lt0; rewrite -bregvNN pbregv_lge0 ?ltev_oppE. Qed.

Lemma nbregv_llt0 x a : x ⊏ 0 -> (f a x ⊏ 0) = (l0 ⊏ a).
Proof. by move=> x_lt0; rewrite -bregvNN pbregv_llt0 ?ltev_oppE. Qed.

Lemma nbregv_lle0 x a : x ⊏ 0 -> (f a x ⊑ 0) = (l0 ⊑ a).
Proof. by move=> x_lt0; rewrite -bregvNN pbregv_lle0 ?ltev_oppE. Qed.

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

Section mx_norm_vnorm.
Variable (K: numDomainType) (m n: nat).

Lemma mx_normvZ (l : K) (x : 'M[K]_(m,n)) : mx_norm (l *: x) = `| l | * mx_norm x.
Proof.
rewrite /= !mx_normE (eq_bigr (fun i => (`|l| * `|x i.1 i.2|)%:nng)); last first.
  by move=> i _; rewrite mxE //=; apply/eqP; rewrite -num_eq /= Num.Theory.normrM.
elim/big_ind2 : _ => // [|a b c d bE dE]; first by rewrite mulr0.
by rewrite !num_max bE dE Num.Theory.maxr_pmulr.
Qed.
Canonical mx_norm_vnorm := Vnorm (@ler_mx_norm_add _ _ _) (@mx_norm_eq0 _ _ _) mx_normvZ.
End mx_norm_vnorm.
Arguments mx_norm_vnorm {K m n}.

Section TrivialMatrix.
Variable (R: ringType).

Lemma mx_dim0n p : all_equal_to (0 : 'M[R]_(0,p)).
Proof. by move=>x/=; apply/matrixP=>i j; destruct i. Qed.
Lemma mx_dimn0 p : all_equal_to (0 : 'M[R]_(p,0)).
Proof. by move=>x/=; apply/matrixP=>i j; destruct j. Qed.
Definition mx_dim0E := (mx_dim0n,mx_dimn0).
Lemma mxf_dim0n T p : all_equal_to ((fun=>0) : T -> 'M[R]_(0,p)).
Proof. by move=>h/=; apply/funext=>i; rewrite mx_dim0E. Qed.
Lemma mxf_dimn0 T p : all_equal_to ((fun=>0) : T -> 'M[R]_(p,0)).
Proof. by move=>h/=; apply/funext=>i; rewrite mx_dim0E. Qed.
Definition mxf_dim0E := (mxf_dim0n,mxf_dimn0).

Definition mx_dim0 := (mx_dim0n,mx_dimn0,mxf_dim0n,mxf_dimn0).

Lemma big_card0 (T : Type) (idx : T) (op : T -> T -> T) (I : finType) 
  (r: seq I) (P : pred I) 
  (F: I -> T): #|I| = 0%N ->
  \big[op/idx]_(i <- r | P i) F i = idx.
Proof.
elim: r. by rewrite big_nil.
move=>a l _ PI. exfalso. move: (fintype0 a)=>//.
Qed.

End TrivialMatrix.


(******************Module for Real matrix********************)
(* show the equivalence between mx_norm and any vector norm *)
(* i.e., exists c1 c2, c1 > 0 & c2 > 0 &                    *)
(*             forall x, c1 * `|x| <= mnorm x <= c2 * `|x|  *)
(* Some lemmas are commented since they are not used        *)
Module realTypeMxCvg.

Section mxvec_norm.
Variable (R: numDomainType) (m n : nat).
Local Notation M := 'M[R]_(m.+1,n.+1).
Import Num.Def Num.Theory.

Lemma mxvec_norm (x : M) : `|x| = `|mxvec x|.
Proof.
apply/le_anti/andP; split; rewrite /normr/=/mx_norm;
rewrite (bigmax_eq_arg (ord0, ord0))// ?ord1 ?num_le.
2,4: by move=>i _; rewrite/= -num_le/=.
by rewrite -mxvecE; apply: (le_trans _ (@ler_bigmax_cond _ _ _ _ _ _ 
  (ord0,(mxvec_index [arg max_(i > (ord0, ord0))`|x i.1 i.2|%:nng]%O.1
  [arg max_(i > (ord0, ord0))`|x i.1 i.2|%:nng]%O.2)) _)).
set k := [arg max_(i > (ord0, ord0))`|mxvec x i.1 i.2|%:nng]%O.2 : 'I_(m.+1*n.+1).
case/mxvec_indexP: k => i j /=; rewrite (mxvecE x i j).
by apply: (le_trans _ (@ler_bigmax_cond _ _ _ _ _ _ (i,j) _)).
Qed.

Lemma mxvec_normV x : `|(vec_mx x : M)| = `|x|.
Proof. by rewrite -{2}(vec_mxK x) mxvec_norm. Qed.
End mxvec_norm.

Section mxvec_continuous.
Variable (R : numFieldType) (m n : nat).

Lemma vec_mx_continuous : continuous (@vec_mx R m.+1 n.+1).
Proof.
move=> x s/= /nbhs_ballP [/=e egt0 Pb].
apply/nbhs_ballP. exists e =>//=.
move=> y /= Pxy. apply (Pb (vec_mx y)). move: Pxy.
by rewrite -!ball_normE/= -linearB/= mxvec_normV.
Qed.

Lemma mxvec_continuous : continuous (@mxvec R m.+1 n.+1).
Proof.
move=> x s/= /nbhs_ballP [/=e egt0 Pb].
apply/nbhs_ballP. exists e =>//=.
move=> y /= Pxy. apply (Pb (mxvec y)). move: Pxy.
by rewrite -!ball_normE/= -{1}(mxvecK x) -{1}(mxvecK y) -linearB/= mxvec_normV.
Qed.
End mxvec_continuous.

Section equal_mx_norm.
Import Num.Def Num.Theory.
Variable (R: realType) (m n : nat).
Local Notation M := 'M[R]_(m.+1,n.+1).
Variable (mnorm : vnorm [lmodType R of M]).

Lemma bound_unit_sphere : bounded_set [set x : M | `|x| = 1%:R].
Proof.
exists 1%:R. split. by rewrite real1.
move=>e egt1 v/= ->. by apply/ltW.
Qed.

Lemma mnorm_sum (I: finType) (r : seq I) (P: pred I) f :
  mnorm (\sum_(i <- r | P i) f i) <= \sum_(i <- r | P i) mnorm (f i).
Proof.
elim: r => [|x r IH]; first by rewrite !big_nil normv0.
rewrite !big_cons. case: (P x)=>//.
apply (le_trans (lev_norm_add _ _ _)). by apply ler_add.
Qed.

Lemma mnorm_ubounded : exists c : R, (0 < c /\ forall x, mnorm x <= c * `|x|).
Proof.
pose c := \big[maxr/0]_i (mnorm (delta_mx i.1 i.2)).
exists ((m.+1 * n.+1)%:R * c). split; last first.
move=>x; rewrite {1}(matrix_sum_delta x) pair_big/=.
apply: (le_trans (mnorm_sum _ _ _)).
have <-: \sum_(i: 'I_m.+1 * 'I_n.+1) (c * `|x|) = (m.+1 * n.+1)%:R * c * `|x|.
by rewrite sumr_const card_prod !card_ord -mulr_natl mulrA.
apply: ler_sum=>/= i _; rewrite normvZ mulrC; apply ler_pmul.
by apply normv_ge0. by apply normr_ge0. rewrite /c. 2: rewrite {2}/normr/= mx_normrE.
1,2: by apply: ler_bigmax_cond.
apply mulr_gt0. by rewrite ltr0n.
rewrite /c. apply/bigmax_gtrP. right. exists (ord0, ord0)=>//=.
rewrite lt_def normv_ge0 andbT. have: (delta_mx ord0 ord0 != (0 : M)).
apply/negP=>/eqP/matrixP/(_ ord0 ord0). rewrite !mxE !eqxx/=.
move/eqP. apply/negP. by apply oner_neq0.
apply contraNN. by move/eqP/normv0_eq0=>->.
Qed.

Lemma open_unit_ball1 (y : R) : open [set x : M | `|x| > y].
Proof.
move=> x /=; rewrite -subr_gt0 => xDy_gt0.
apply/nbhs_ballP; exists (`|x| - y) => // z.
rewrite -ball_normE/= ltr_subr_addl -ltr_subr_addr=>P.
apply (lt_le_trans P). rewrite -{1}(normrN x).
move: (ler_sub_norm_add (-x) (x-z)).
by rewrite addKr !normrN.
Qed.

Lemma open_unit_ball2 (y : R) : open [set x : M | `|x| < y].
Proof.
move=> x /=; rewrite -subr_gt0 => xDy_gt0.
apply/nbhs_ballP; exists (y - `|x|) => // z.
rewrite -ball_normE/= ltr_subr_addl=>P.
apply: (le_lt_trans _ P).
move: (ler_norm_add (-x) (x-z)).
by rewrite addKr !normrN.
Qed.

Lemma closed_unit_sphere : closed [set x : M | `|x| = 1%:R].
Proof.
rewrite (_ : mkset _ = ~` [set x | `| x | > 1%:R] `&` ~` [set x | `| x | < 1%:R]).
apply closedI; rewrite closedC. apply open_unit_ball1. apply open_unit_ball2.
rewrite predeqE => x /=; split; first by move=>->; rewrite !ltxx.
move=>[/negP P1 /negP P2].
move: P1 P2. rewrite !real_ltNge ?real1// !negbK=>/le_gtF P1.
by rewrite le_eqVlt P1 orbF=>/eqP <-.
Qed.

Lemma mxvec_bounded_set (A: set M) :
  bounded_set A <-> bounded_set (mxvec @` A).
Proof.
split; move=>[e [P1 P2]]; exists e; split=>// x Px y/=.
move=> [z Pz eqzy]. move: (P2 x Px)=>/(_ z Pz)/=. 
by rewrite -eqzy mxvec_norm.
move: (P2 x Px)=>/(_ (mxvec y))/= P Py.
rewrite mxvec_norm. apply P. by exists y.
Qed.

Lemma mxvec_open_set (A: set M) :
  open A <-> open (mxvec @` A).
Proof.
rewrite !openE; split=>/=.
move=>P1 y/= [x Px eqxy].
move: (P1 x Px) => /=. rewrite /interior.
move/nbhs_ballP=>[/=e egt0 Pb].
apply/nbhs_ballP. exists e=>// z/= Pz.
exists (vec_mx z). apply Pb. move: Pz.
by rewrite -!ball_normE/= -(mxvecK x) -linearB/= mxvec_normV eqxy.
by rewrite vec_mxK.
move=>P1 y/= Py. 
have P3: (exists2 x : 'M_(m.+1, n.+1), A x & mxvec x = mxvec y) by exists y.
move: (P1 (mxvec y) P3). rewrite /interior.
move/nbhs_ballP=>[/=e egt0 Pb].
apply/nbhs_ballP. exists e=>// z/= Pz.
move: Pz (Pb (mxvec z)).
rewrite -!ball_normE/= mxvec_norm linearB/= =>P4 P5.
move: (P5 P4)=>[t Pt] /eqP. by rewrite (inj_eq (can_inj mxvecK))=>/eqP <-.
Qed.

Lemma mxvec_setN (A: set M) : ~` [set mxvec x | x in A] = [set mxvec x | x in ~` A].
Proof.
rewrite seteqP. split=>x/=; rewrite -forall2NP.
move=>/(_ (vec_mx x)). rewrite vec_mxK =>[[|//]]. exists (vec_mx x)=>//.
by rewrite vec_mxK.
move=>[y Py eqxy] z. case E: (y == z).
left. by move/eqP: E=><-. right. 
rewrite -eqxy=>/eqP. by rewrite (inj_eq (can_inj mxvecK)) eq_sym E.
Qed.

Lemma mxvec_closed_set (A: set M) :
  closed A <-> closed (mxvec @` A).
Proof.
split. by rewrite -openC mxvec_open_set -closedC -{2}(setCK A) -mxvec_setN.
by rewrite -openC mxvec_setN -mxvec_open_set -closedC setCK.
Qed.

Lemma bounded_closed_compact_mx (A : set M) :
  bounded_set A -> closed A -> compact A.
Proof.
move=>/mxvec_bounded_set P1 /mxvec_closed_set P2.
have: compact (vec_mx @` (mxvec @` A)).
apply: (continuous_compact _ (bounded_closed_compact P1 P2)). 
apply/continuous_subspaceT=>x _; apply: vec_mx_continuous.
have ->//: [set vec_mx x | x in [set mxvec x | x in A]] = A.
rewrite seteqP. split=>x/=.
move=>[y [z Pz]] <- <-. by rewrite mxvecK.
move=>Px. exists (mxvec x). by exists x. by rewrite mxvecK.
Qed.

Lemma compact_unit_sphere : compact [set x : M | `|x| = 1%:R].
Proof. apply (bounded_closed_compact_mx bound_unit_sphere closed_unit_sphere). Qed.

Lemma continuous_mnorm : continuous mnorm.
Proof.
move: mnorm_ubounded => [c [cgt0 mnormb]].
move=> x s/= /nbhs_ballP [/=e egt0 Pb].
apply/nbhs_ballP. exists (e / c) =>//=; first by apply divr_gt0.
move=> y /= Pxy. apply (Pb (mnorm y)). move: Pxy. 
rewrite mx_norm_ball /ball /= => P1.
apply (le_lt_trans (lev_dist_dist _ x y)). 
apply (le_lt_trans (mnormb (x - y))).
by rewrite mulrC -ltr_pdivl_mulr.
Qed.

Lemma compact_unit_sphere_vint : compact (mnorm @` [set x : M | `|x| = 1%:R]).
Proof. apply continuous_compact. apply/continuous_subspaceT.
move=>x _; apply continuous_mnorm.
apply compact_unit_sphere.
Qed.

Lemma mx_norm_natmul (x : M) k : mx_norm (x *+ k) = (mx_norm x) *+ k.
Proof.
rewrite [in RHS]/mx_norm; elim: k => [|k ih]; first by rewrite !mulr0n mx_norm0.
rewrite !mulrS; apply/eqP; rewrite eq_le; apply/andP; split.
  by rewrite -ih; exact/ler_mx_norm_add.
have [/mx_norm_eq0->|x0] := eqVneq (mx_norm x) 0.
  by rewrite -/(mx_norm 0) -/(mx_norm 0) !(mul0rn,addr0,mx_norm0).
rewrite -/(mx_norm x) -num_abs_le; last by rewrite mx_normE.
apply/bigmax_gerP; right => /=.
have [i Hi] := mx_norm_neq0 x0.
exists i => //; rewrite Hi -!mulrS -normrMn mulmxnE.
by rewrite le_eqVlt; apply/orP; left; apply/eqP/val_inj => /=; rewrite normr_id.
Qed.

Lemma unit_sphere_neq0 : (mnorm @` [set x : M | `|x| = 1%:R]) !=set0.
Proof.
exists (mnorm (const_mx 1))=>/=. exists (const_mx 1)=>//.
rewrite /normr/= mx_normrE. under eq_bigr do rewrite mxE.
apply/eqP. rewrite eq_le. apply/andP. split; last first.
by apply/bigmax_gerP=>/=; right; exists (ord0,ord0)=>//; rewrite normr1.
by apply/bigmax_lerP; split=>// i j; rewrite normr1.
Qed.

Lemma mnorm_lbounded : exists c : R, (0 < c /\ forall x,  c * `|x| <= mnorm x).
Proof.
move: (compact_min compact_unit_sphere_vint unit_sphere_neq0)=>[c [v /= Pv1 Pv2] Py].
have Pc: 0 < c by rewrite -Pv2 normv_gt0 -normr_gt0 Pv1 ltr01.
exists c. split=>//.
move=>x. case E: (x == 0).
move: E=>/eqP ->. by rewrite normr0 normv0 mulr0.
have E1: `|x| > 0 by rewrite normr_gt0 E.
rewrite -{2}(scale1r x) -(@mulfV _ `|x|); last by move: E1; rewrite lt_def=>/andP[->].
rewrite -scalerA normvZ normr_id mulrC. apply ler_pmul=>//.
by apply ltW. apply Py. exists (`|x|^-1 *: x)=>//.
rewrite mx_normZ ger0_norm ?inv_nng_ge0// mulVf//.
by move: E1; rewrite lt_def=>/andP[->].
Qed.

End equal_mx_norm. 
End realTypeMxCvg.


(***********************Complex Matrix***********************)
Import realTypeMxCvg.

(*Remark: 'M_(0,m) and 'M_(m,0) are not canonical to normedZmodType 
  (normedtype does not adopt it) and matrix_normedModType
  (this is impossible without changing the definition of ball of matrix).
  On the other hand, we can talk about convergence on 'M_(0,m) and 'M_(m,0);
  In particular, when dimension is packed, we are not able to always find 
  .+1 structure. So in this section, all the properties are proved for 'M_(m,n)
  even if it's trivial  *)

Section cmx_seq_composition.
Variable (R: realType) (m n : nat).
Local Notation C := R[i].
Local Notation M := 'M[C]_(m,n).
Implicit Type (f g: nat -> M) (r: nat) (a b : M) (s : nat -> C) (k: C).

Lemma Cmxhausdorff p q : hausdorff_space [topologicalType of 'M[C]_(p,q)].
Proof.
case: p=>[|p]; last first. case: q=>[|q]; last by apply: norm_hausdorff.
all: rewrite ball_hausdorff=>/=a b /negP Pab; exfalso; apply Pab; apply/eqP;
apply/matrixP=>i j. by destruct j. by destruct i.
Qed.

Lemma cmxcvg_limE f a : f --> a <-> lim f = a /\ cvg f.
Proof. 
split=>[P1|[ <-]//]. split. apply/cvg_lim. apply Cmxhausdorff.
apply P1. by move: P1=>/cvgP.
Qed.

Lemma cmxcvg_dim0n p (h: nat -> 'M[C]_(0,p)) (x : 'M[C]_(0,p)) : h --> x.
Proof. by rewrite !mx_dim0; apply: cvg_cst. Qed.
Lemma cmxcvg_dimn0 p (h: nat -> 'M[C]_(p,0)) (x : 'M[C]_(p,0)) : h --> x.
Proof. by rewrite !mx_dim0; apply: cvg_cst. Qed.
Lemma is_cmxcvg_dim0n p (h: nat -> 'M[C]_(0,p)) : cvg h.
Proof. by apply/cvg_ex; exists 0; apply cmxcvg_dim0n. Qed.
Lemma is_cmxcvg_dimn0 p (h: nat -> 'M[C]_(p,0)) : cvg h.
Proof. by apply/cvg_ex; exists 0; apply cmxcvg_dimn0. Qed.

(* for quick use. directly use these lemmas have the problem on different canonical routes *)

Lemma cmxcvg_cst a : (fun n:nat=>a) --> a. Proof. exact: cvg_cst. Qed.
Lemma is_cmxcvg_cst a : cvg (fun n:nat=>a). Proof. exact: is_cvg_cst. Qed.
Lemma cmxlim_cst a : lim (fun n:nat=>a) = a. Proof. apply: lim_cst. apply Cmxhausdorff. Qed.

Lemma cmxcvgN f a : f --> a -> (- f) --> - a.
Proof.
case: m f a=>[f a _|m' f a]; [apply cmxcvg_dim0n|].
case: n f a=>[f a _|n' f a]; [apply cmxcvg_dimn0|exact: cvgN].
Qed.

Lemma is_cmxcvgN f : cvg f -> cvg (- f).
Proof. by move=> /cmxcvgN /cvgP. Qed.

Lemma is_cmxcvgNE f : cvg (- f) = cvg f.
Proof. by rewrite propeqE; split=> /cmxcvgN; rewrite ?opprK => /cvgP. Qed.

Lemma cmxcvgMn f r a : f --> a -> ((@GRing.natmul _)^~r \o f) --> a *+ r.
Proof.
case: m f a=>[f a _|m' f a]; [apply cmxcvg_dim0n|].
case: n f a=>[f a _|n' f a]; [apply cmxcvg_dimn0|exact: cvgMn].
Qed.

Lemma is_cmxcvgMn f r : cvg f -> cvg ((@GRing.natmul _)^~r \o f).
Proof. by move=> /(@cmxcvgMn _ r) /cvgP. Qed.

Lemma cmxcvgD f g a b : f --> a -> g --> b -> (f + g) --> a + b.
Proof.
case: m f g a b=>[f g a b _ _|m' f g a b]; [apply cmxcvg_dim0n|].
case: n f g a b=>[f g a b _ _|n' f g a b]; [apply cmxcvg_dimn0|exact: cvgD].
Qed.

Lemma is_cmxcvgD f g : cvg f -> cvg g -> cvg (f + g).
Proof. by have := cvgP _ (cmxcvgD _ _); apply. Qed.

Lemma cmxcvgB f g a b : f --> a -> g --> b -> (f - g) --> a - b.
Proof. by move=> ? ?; apply: cmxcvgD=>[//|]; apply: cmxcvgN. Qed.

Lemma is_cmxcvgB f g : cvg f -> cvg g -> cvg (f - g).
Proof. by have := cvgP _ (cmxcvgB _ _); apply. Qed.

Lemma is_cmxcvgDlE f g : cvg g -> cvg (f + g) = cvg f.
Proof.
move=> g_cvg; rewrite propeqE; split; last by move=> /is_cmxcvgD; apply.
by move=> /is_cmxcvgB /(_ g_cvg); rewrite addrK.
Qed.

Lemma is_cmxcvgDrE f g : cvg f -> cvg (f + g) = cvg g.
Proof. by rewrite addrC; apply: is_cmxcvgDlE. Qed.

Lemma cmxcvgZ s f k a : s --> k -> f --> a -> (fun x => s x *: f x) --> k *: a.
Proof.
case: m f a=>[f a _ _|m' f a]; [apply cmxcvg_dim0n|].
case: n f a=>[f a _ _|n' f a]; [apply cmxcvg_dimn0|exact: cvgZ].
Qed.

Lemma is_cmxcvgZ s f : cvg s -> cvg f -> cvg (fun x => s x *: f x).
Proof. by have := cvgP _ (cmxcvgZ _ _); apply. Qed.

Lemma cmxcvgZl s k a : s --> k -> (fun x => s x *: a) --> k *: a.
Proof. by move=> ?; apply: cmxcvgZ => //; exact: cvg_cst. Qed.

Lemma is_cmxcvgZl s a : cvg s -> cvg (fun x => s x *: a).
Proof. by have := cvgP _ (cmxcvgZl  _); apply. Qed.

Lemma cmxcvgZr k f a : f --> a -> k \*: f --> k *: a.
Proof. apply: cmxcvgZ => //; exact: cvg_cst. Qed.

Lemma is_cmxcvgZr k f : cvg f -> cvg (k *: f ).
Proof. by have := cvgP _ (cmxcvgZr  _); apply. Qed.

Lemma is_cmxcvgZrE k f : k != 0 -> cvg (k *: f) = cvg f.
Proof.
move=> k_neq0; rewrite propeqE; split => [/(@cmxcvgZr k^-1)|/(@cmxcvgZr k)/cvgP//].
by under [_ \*: _]funext => x /= do rewrite scalerK//; apply: cvgP.
Qed.

Lemma cmxlimN f : cvg f -> lim (- f) = - lim f.
Proof. by move=> ?; apply: cvg_lim; [apply Cmxhausdorff|apply: cmxcvgN]. Qed.

Lemma cmxlimD f g : cvg f -> cvg g -> lim (f + g) = lim f + lim g.
Proof. move=> Pf Pg; apply: cvg_lim; [apply Cmxhausdorff|apply: cmxcvgD;[apply Pf|apply Pg]]. Qed.

Lemma cmxlimB f g : cvg f -> cvg g -> lim (f - g) = lim f - lim g.
Proof. move=> Pf Pg; apply: cvg_lim; [apply Cmxhausdorff|apply: cmxcvgB;[apply Pf|apply Pg]]. Qed.

Lemma cmxlimZ s f : cvg s -> cvg f -> lim (fun x => s x *: f x) = lim s *: lim f.
Proof. move=> Ps Pf; apply: cvg_lim; [apply Cmxhausdorff|apply: cmxcvgZ;[apply Ps|apply Pf]]. Qed.

Lemma cmxlimZl s a : cvg s -> lim (fun x => s x *: a) = lim s *: a.
Proof. by move=> ?; apply: cvg_lim; [apply Cmxhausdorff|apply: cmxcvgZl]. Qed.

Lemma cmxlimZr k f : cvg f -> lim (k *: f) = k *: lim f.
Proof. by move=> ?; apply: cvg_lim; [apply Cmxhausdorff|apply: cmxcvgZr]. Qed.

(* since only nontrivial matrix are canonical to normZmodType *)
Lemma cmxcvg_norm (h : nat->'M[C]_(m.+1,n.+1)) (x : 'M[C]_(m.+1,n.+1)) : 
  h --> x -> (Num.norm \o h) --> `|x|.
Proof. exact: cvg_norm. Qed.
Lemma is_cmxcvg_norm (h : nat->'M[C]_(m.+1,n.+1)) : 
  cvg h -> cvg (Num.norm \o h).
Proof. exact: is_cvg_norm. Qed.
Lemma cmxlim_norm (h : nat->'M[C]_(m.+1,n.+1)) : 
  cvg h -> lim (Num.norm \o h) = `|lim h|.
Proof. exact: lim_norm. Qed.

Lemma cmxcvg_map f a (V : completeType) (h : M -> V) :
  continuous h -> f --> a -> (h \o f) --> h a.
Proof. 
move=>ch cvgf; apply: (@cvg_fmap _ _ [filter of f] a h).
by apply ch. by apply cvgf.
Qed.

Lemma cmxcvg_mapV (V : completeType) (h : V -> M) (h' : nat -> V) (a : V) :
  continuous h -> h' --> a -> (h \o h') --> h a.
Proof. 
move=>ch cvgf; apply: (@cvg_fmap _ _ [filter of h'] a h).
by apply ch. by apply cvgf.
Qed.

Lemma is_cmxcvg_map f (V : completeType) (h : M -> V) :
  continuous h -> cvg f -> cvg (h \o f).
Proof.
move=>P1 /cvg_ex=>[/= [a Pa]]. apply/cvg_ex.
exists (h a). by move: (cmxcvg_map P1 Pa).
Qed.

Lemma is_cmxcvg_mapV (V : completeType) (h : V -> M) (h' : nat -> V) :
  continuous h -> cvg h' -> cvg (h \o h').
Proof.
move=>P1 /cvg_ex=>[/= [a Pa]]. apply/cvg_ex.
exists (h a). by move: (cmxcvg_mapV P1 Pa).
Qed.

Lemma cmxlim_map f a (V : completeType) (h : M -> V) :
  hausdorff_space V -> continuous h -> cvg f -> lim (h \o f) = h (lim f).
Proof. by move=>hV ch; move/(cmxcvg_map ch)/cvg_lim=>/(_ hV). Qed.

Lemma cmxlim_mapV (V : completeType) (h : V -> M) (h' : nat -> V) :
  continuous h -> cvg h' -> lim (h \o h') = h (lim h').
Proof. by move=>ch; move/(cmxcvg_mapV ch)/cvg_lim=>/(_ (@Cmxhausdorff _ _)). Qed.

Lemma is_cmxcvgZlE s a : a != 0 -> cvg (fun x => s x *: a) = cvg s.
Proof.
move=> a_neq0; rewrite propeqE; split; last by apply is_cmxcvgZl.
have [i [j Pij]] : exists i j, a i j != 0.
move: a_neq0. apply contraPP. rewrite -forallNP=>P.
apply/negP. rewrite negbK. apply/eqP/matrixP=>i j.
move: (P i). rewrite -forallNP=>/(_ j)/negP. by rewrite mxE negbK=>/eqP->.
set t := (fun x : M => (x i j) / (a i j)).
have P1: s = t \o (fun x : nat => s x *: a).
rewrite funeqE=>p. rewrite /= /t mxE mulrK//.
move=>P. rewrite P1. apply/is_cmxcvg_map=>//.
move=>/= x w/= /nbhs_ballP [/=e egt0 Pb].
apply/nbhs_ballP. have P2: 0 < `|a i j|.
rewrite lt_def Num.Theory.normr_ge0 andbT.
by move: Pij; apply contraNN=>/eqP/Num.Theory.normr0P.
exists (e * `|a i j|) =>//=. apply Num.Theory.mulr_gt0=>//.
move=> y /= Pxy. apply (Pb (t y)). move: Pxy.
rewrite /ball/= /mx_ball=>/(_ i j). rewrite /ball/=.
rewrite /t -mulrBl Num.Theory.normrM Num.Theory.normrV ?GRing.unitfE//.
rewrite Num.Theory.ltr_pdivr_mulr// =>P3.
Qed.

Lemma mx_normEV p q : (@mx_norm _ _ _ : 'M[C]_(p.+1,q.+1) -> C) = (@Num.Def.normr _ _).
Proof. by apply/funext. Qed.

Lemma cmxcvg_limP p q (h: nat -> 'M[C]_(p,q)) (x : 'M[C]_(p,q)) :
  h --> x <-> forall e, 0 < e -> exists N, forall n,  (N <= n)%N -> mx_norm (h n - x) < e.
Proof.
case: p h x=>[h x|p]; last case: q=>[h x|q h x].
1,2: split=>_; [move=>e Pe; exists 0%N=>r _; rewrite !mx_dim0 mx_norm0//|].
apply cmxcvg_dim0n. apply cmxcvg_dimn0. rewrite mx_normEV.
exact: (@cvg_limP _ [completeNormedModType C of 'M_(p.+1, q.+1)] h x).
Qed.

Lemma cmxcvg_subseqP p q (h: nat -> 'M[C]_(p,q)) (x : 'M[C]_(p,q)) : 
  h --> x <-> (forall (h': nat -> nat), (forall n, (h' n.+1 > h' n)%N) -> (h \o h') --> x).
Proof.
case: p h x=>[h x|p]; last case: q=>[h x|q h x].
1,2: split=>_; [move=>??|]; rewrite !mx_dim0; apply: cvg_cst.
exact: (@cvg_subseqP _ [completeNormedModType C of 'M_(p.+1, q.+1)] h x).
Qed.

Lemma cmxcvg_subseqPN p q (h: nat -> 'M[C]_(p,q)) (x : 'M[C]_(p,q)) :
  ~ (h --> x) <-> exists e (h': nat -> nat), 
    (forall n, (h' n.+1 > h' n)%N) /\ 0 < e /\ (forall n, mx_norm ((h \o h') n - x) >= e).
Proof.
case: p h x=>[h x|p]; last case: q=>[h x|q h x].
1,2: rewrite not_existsP; rewrite iff_not2; split=>_;[|rewrite !mx_dim0; apply: cvg_cst].
1,2: move=>c; rewrite -forallNP=> h'; rewrite !not_andP; right.
1,2: case E: (0 < c); [right|left=>//]; rewrite -existsNP; exists 0%N; rewrite !mx_dim0 mx_norm0.
1,2: by apply/negP; rewrite -Num.Theory.real_ltNge// ?Num.Theory.real0// Num.Theory.gtr0_real.
rewrite mx_normEV.
exact: (@cvg_subseqPN _ [completeNormedModType C of 'M_(p.+1, q.+1)] h x).
Qed.

Lemma cmxnatmul_continuous p : continuous (fun x : M => x *+ p).
Proof.
case: m=>/=[x|m']; last case: n=>/=[x|n' x].
1,2: rewrite !mx_dim0; apply: cst_continuous.
exact: natmul_continuous.
Qed.

Lemma cmxscale_continuous : continuous (fun z : C * M => z.1 *: z.2).
Proof.
case: m=>/=[x|m']; last case: n=>/=[x|n' x].
1,2: rewrite !mx_dim0; apply: cst_continuous.
exact: scale_continuous.
Qed.

Arguments cmxscale_continuous _ _ : clear implicits.

Lemma cmxscaler_continuous k : continuous (fun x : M => k *: x).
Proof.
by move=> x; apply: (cvg_comp2 (cvg_cst _) cvg_id (cmxscale_continuous (_, _))).
Qed.

Lemma cmxscalel_continuous (x : M) : continuous (fun k : C => k *: x).
Proof.
by move=> k; apply: (cvg_comp2 cvg_id (cvg_cst _) (cmxscale_continuous (_, _))).
Qed.

(* TODO: generalize to pseudometricnormedzmod *)
Lemma cmxopp_continuous : continuous (fun x : M => -x).
Proof.
case: m=>/=[x|m']; last case: n=>/=[x|n' x].
1,2: rewrite !mx_dim0; apply: cst_continuous.
exact: opp_continuous.
Qed.

Lemma cmxadd_continuous : continuous (fun z : M * M => z.1 + z.2).
Proof.
case: m=>/=[x|m']; last case: n=>/=[x|n' x].
1,2: rewrite !mx_dim0; apply: cst_continuous.
exact: add_continuous.
Qed.

Arguments cmxadd_continuous _ _ : clear implicits.

Lemma cmxaddr_continuous a : continuous (fun z : M => a + z).
Proof.
by move=> x; apply: (cvg_comp2 (cvg_cst _) cvg_id (cmxadd_continuous (_, _))).
Qed.

Lemma cmxaddl_continuous a : continuous (fun z : M => z + a).
Proof.
by move=> x; apply: (cvg_comp2 cvg_id (cvg_cst _) (cmxadd_continuous (_, _))).
Qed.

(* Variable (f : nat -> 'M[R[i]]_(m,n)) (a : 'M[R[i]]_(m,n)). *)
Definition cmxcauchy_seq f := 
  forall e, 0 < e -> exists N, forall i j, 
  (N <= i)%N -> (N <= j)%N -> mx_norm (f i - f j) < e.

Definition cmxcvg_seq f a := 
  forall e, 0 < e -> exists N : nat, 
    forall i, (N <= i)%N -> mx_norm (a - f i) < e.

Lemma cmxcauchy_seqP f : cmxcauchy_seq f <-> cvg f.
Proof.
rewrite /cmxcauchy_seq; case: m f=>[f|]; last case: n=>[m' f|m' n' f].
1,2: split=>_. apply/is_cmxcvg_dim0n. 2: apply/is_cmxcvg_dimn0.
1,2: by move=>e egt0; exists 0%N=>i j _ _; rewrite !mx_dim0 mx_norm0.
exact: (@cauchy_seqP _ [completeNormedModType R[i] of 'M[R[i]]_(n'.+1,m'.+1)]).
Qed.

Lemma cmxcvg_seqP f a : cmxcvg_seq f a <-> f --> a.
Proof.
rewrite /cmxcvg_seq; case: m f a=>[f a|]; last case: n=>[m' f a|m' n' f a].
1,2: split=>[_ |_ e egt0]; last exists 0%N=>i _. 
1,2,3,4: rewrite !mx_dim0 ?mx_norm0//. apply/cmxcvg_dim0n. apply/cmxcvg_dimn0.
exact: (@cvg_seqP _ [completeNormedModType R[i] of 'M[R[i]]_(n'.+1,m'.+1)]).
Qed.

End cmx_seq_composition.

Section cmx_linear_continuous.
Variable (R: realType).
Local Notation C := R[i].

Import Num.Theory ComplexField Num.Def complex.

Lemma mx_normcE m n (x : 'M[C]_(m,n)) :
  mx_norm x = \big[maxr/0]_ij `| x ij.1 ij.2|.
Proof.
rewrite /mx_norm; apply/esym.
elim/big_ind2 : _ => //= a a' b b' ->{a'} ->{b'}.
case: (leP a b) => ab; by [rewrite max_r | rewrite max_l // ltW].
Qed.

Lemma bigmax_eqc I (r : seq I) (F : I -> R) (x : R) :
  \big[maxr/x%:C]_(i <- r) (F i)%:C = (\big[maxr/x]_(i <- r) (F i))%:C.
Proof.
elim: r. by rewrite !big_nil.
move=>a r IH. rewrite !big_cons IH /maxr ltcR /maxr.
by case: ltP.
Qed.

Lemma mx_normcE1 m n (x : 'M[C]_(m,n)) :
  mx_norm x = (\big[maxr/0]_ij Re `| x ij.1 ij.2|)%:C.
rewrite mx_normcE -bigmax_eqc.
apply eq_bigr=>i _. set t := `|x i.1 i.2|.
have: 0 <= t. rewrite /t normr_ge0//.
rewrite -{2}(complex_split t) lecE=>/andP[/eqP-> _].
by rewrite addr0.
Qed.

Lemma mx_norm_element m n (x : 'M[C]_(m.+1,n.+1)) :
  forall i, `|x i.1 i.2| <= `|x|.
Proof.
move=>i. rewrite {2}/normr/= mx_normcE1.
rewrite lecE/= eqxx/=. apply: ler_bigmax.
Qed.

Lemma ltr_sum n (F G : 'I_n.+1 -> C) :
    (forall i, F i < G i) ->
  \sum_(i < n.+1) F i < \sum_(i < n.+1) G i.
Proof.
move: F G. elim: n.
by move=>F G IH; rewrite !big_ord1 IH.
move=>m IH F G IH1.
rewrite big_ord_recl [\sum_(i < m.+2) G i]big_ord_recl.
apply ltr_add. by apply IH1.
apply IH=>i. apply IH1.
Qed.

Lemma ler_sum_const (T: numDomainType) m (f : 'I_m -> T) c :
  (forall i, f i <= c) ->
  \sum_i f i <= m%:R * c.
Proof.
move=>P1; have P2: \sum_i f i <= \sum_(i<m) c. by apply ler_sum.
apply: (le_trans P2); by rewrite sumr_const card_ord mulr_natl.
Qed.

Lemma cmxlinear_continuous m n p q (f : 'M[C]_(m,n) -> 'M[C]_(p,q)) :
  linear f -> continuous f.
Proof.
move: f; case: m=>[|m]; last first. case: n=>[|n]; last first. 
case: p=>[|p]; last first. case: q=>[|q]; last first.
all: move=>f Lf; set LfT := Linear Lf; have P0 : f = LfT by [].
suff: continuous LfT by [].
rewrite -linear_bounded_continuous -bounded_funP=>r/=.
have Pu : exists c, forall i j, `|LfT (delta_mx i j)| <= c.
exists (\sum_i\sum_j`|LfT (delta_mx i j)|)=>i j.
rewrite (bigD1 i)//= (bigD1 j)//= -addrA Num.Theory.ler_addl Num.Theory.addr_ge0//.
1,2: rewrite Num.Theory.sumr_ge0//. move=>k _; rewrite Num.Theory.sumr_ge0//.
move: Pu=>[c Pc]. exists ((m.+1)%:R * ((n.+1)%:R * (r * c)))=>x Px.
have Pij i j : `|x i j| <= r by apply (le_trans (mx_norm_element _ (i,j))).
rewrite (matrix_sum_delta x) P0 linear_sum/=.
apply: (le_trans (ler_norm_sum _ _ _)). apply/ler_sum_const=>i.
rewrite P0 linear_sum/=.
apply: (le_trans (ler_norm_sum _ _ _)). apply/ler_sum_const=>j.
by rewrite P0 linearZ/= normmZ ler_pmul.
all: have ->: f = (fun=>0). 2,4,6,8: apply: cst_continuous.
all: apply/funext=>i. all: rewrite mx_dim0E// P0 linear0//.
Qed.

Lemma cmxcvg_lfun m n p q (f : 'M[C]_(m,n) -> 'M[C]_(p,q))
  (u : nat -> 'M[C]_(m,n)) (a : 'M[C]_(m,n)) : 
  linear f -> u --> a -> (fun x=> f (u x)) --> (f a).
Proof. by move/cmxlinear_continuous=>P1; apply: continuous_cvg; apply: P1. Qed.

Lemma is_cmxcvg_lfun m n p q (f : 'M[C]_(m,n) -> 'M[C]_(p,q))
(u : nat -> 'M[C]_(m,n))  : linear f -> cvg u -> cvg (f \o u).
Proof. by move=>P1; have := cvgP _ (cmxcvg_lfun P1 _); apply. Qed.

Lemma cmxlim_lfun m n p q (f : 'M[C]_(m,n) -> 'M[C]_(p,q))
  (u : nat -> 'M[C]_(m,n)) : 
  linear f -> cvg u -> lim (f \o u) = f (lim u).
Proof. move=>P1 ?; apply: cvg_lim => //. apply Cmxhausdorff. by apply: cmxcvg_lfun. Qed.

Lemma cmxclosed_comp m n p q (f : 'M[C]_(m,n) -> 'M[C]_(p,q))
  (A : set 'M[C]_(p,q)) :
  linear f -> closed A -> closed (f @^-1` A).
Proof. by move=>lf; apply closed_comp=>x _; apply (cmxlinear_continuous lf). Qed.

Lemma cmxopen_comp m n p q (f : 'M[C]_(m,n) -> 'M[C]_(p,q))
  (A : set 'M[C]_(p,q)) :
  linear f -> open A -> open (f @^-1` A).
Proof. by move=>lf; apply open_comp=>x _; apply (cmxlinear_continuous lf). Qed.

Lemma cmxscalar_continuous m n (f : 'M[C]_(m,n) -> C) :
  scalar f -> continuous f.
Proof.
move: f; case: m=>[|m]; last first. case: n=>[|n]; last first.
all: move=>f Lf; set LfT := Linear Lf; have P0 : f = LfT by [].
suff: continuous LfT by [].
rewrite -linear_bounded_continuous -bounded_funP=>r/=.
have Pu : exists c, forall i j, `|LfT (delta_mx i j)| <= c.
exists (\sum_i\sum_j`|LfT (delta_mx i j)|)=>i j.
rewrite (bigD1 i)//= (bigD1 j)//= -addrA ler_addl addr_ge0//.
1,2: rewrite sumr_ge0//. move=>k _. rewrite sumr_ge0//.
move: Pu=>[c Pc]. exists ((m.+1)%:R * ((n.+1)%:R * (r * c)))=>x Px.
have Pij i j : `|x i j| <= r by apply (le_trans (mx_norm_element _ (i,j))).
rewrite (matrix_sum_delta x) P0 linear_sum/=.
apply: (le_trans (ler_norm_sum _ _ _)). apply/ler_sum_const=>i.
rewrite P0 linear_sum/=.
apply: (le_trans (ler_norm_sum _ _ _)). apply/ler_sum_const=>j.
by rewrite P0 linearZ/= normmZ ler_pmul.
all: have ->: f = (fun=>0). 2,4: apply: cst_continuous.
all: apply/funext=>i. all: rewrite mx_dim0E// P0 linear0//.
Qed.

Lemma cmxcvg_sfun m n (f : 'M[C]_(m,n) -> C)
  (u : nat -> 'M[C]_(m,n)) (a : 'M[C]_(m,n)) : 
  scalar f -> u --> a -> (fun x=> f (u x)) --> (f a).
Proof. by move/cmxscalar_continuous=>P1; apply: continuous_cvg; apply: P1. Qed.

Lemma is_cmxcvg_sfun m n (f : 'M[C]_(m,n) -> C)
(u : nat -> 'M[C]_(m,n)) : scalar f -> cvg u -> cvg (f \o u).
Proof. by move=>P1; have := cvgP _ (cmxcvg_sfun P1 _); apply. Qed.

Lemma cmxlim_sfun m n (f : 'M[C]_(m,n) -> C)
  (u : nat -> 'M[C]_(m,n)) : 
  scalar f -> cvg u -> lim (f \o u) = f (lim u).
Proof. move=>P1 ?; apply: cvg_lim => //. by apply: cmxcvg_sfun. Qed.

Lemma cmxcclosed_comp m n (f : 'M[C]_(m,n) -> C)
  (A : set C) :
  scalar f -> closed A -> closed (f @^-1` A).
Proof. by move=>lf; apply closed_comp=>x _; apply (cmxscalar_continuous lf). Qed.

Lemma cmxcopen_comp m n (f : 'M[C]_(m,n) -> C)
  (A : set C) :
  scalar f -> open A -> open (f @^-1` A).
Proof. by move=>lf; apply open_comp=>x _; apply (cmxscalar_continuous lf). Qed.

End cmx_linear_continuous.

(* construct linear bijective functions: complex matrix <--> real vector *)
Section complex_mx2vec.
Import ComplexField.
Variable (R: realType) (m n : nat).
Local Notation C := R[i].

Definition cmxvec (x : 'M[C]_(m,n)) := 
    row_mx (mxvec (map_mx (@Re _) x)) (mxvec (map_mx (@Im _) x)).

Definition cvec_mx (u : 'rV[R]_(m * n + m * n)) := 
  map_mx (fun x=> x%:C) (vec_mx (lsubmx u)) + 
    map_mx (fun x=> x%:Ci) ( vec_mx (rsubmx u)).

Lemma cmxvec_is_additive : additive cmxvec.
Proof. by move=>x y; rewrite /cmxvec -!map_mxvec !raddfB/= opp_row_mx add_row_mx. Qed.

Lemma cvec_mx_is_additive : additive cvec_mx.
Proof.
move=>x y; rewrite /cvec_mx !map_vec_mx.
rewrite !raddfB/= (@map_mxB _ _ (im_complex_additive R))/= !linearB/= linearD/= !addrA.
congr (_ + _). rewrite -!addrA. congr (_ + _). by rewrite addrC.
Qed.

Canonical cmxvec_additive := Additive cmxvec_is_additive.
Canonical cvec_mx_additive := Additive cvec_mx_is_additive.

Lemma cvec_mxK : cancel cvec_mx cmxvec.
Proof. 
move=>x. rewrite /cvec_mx raddfD/= /cmxvec add_row_mx -!map_mxvec !vec_mxK.
by rewrite -[RHS]hsubmxK; congr (row_mx _ _); rewrite /map_mx; 
  apply/matrixP=>i j; rewrite !mxE/= ?addr0 ?add0r. 
Qed.

Lemma cmxvecK : cancel cmxvec cvec_mx.
Proof.
move=>x. rewrite /cvec_mx /cmxvec row_mxKl row_mxKr !mxvecK.
by apply/matrixP=>i j; rewrite !mxE/= complex_split.
Qed.

Lemma cmxvecZ (c : R) x : cmxvec (c%:C *: x) = c *: cmxvec x.
Proof.
rewrite /cmxvec scale_row_mx -!linearZ/=. 
by congr (row_mx (mxvec _) (mxvec _)); apply/matrixP=>i j; rewrite !mxE; 
set y := x i j; destruct y=>/=; rewrite mul0r ?subr0 ?addr0.
Qed.

Lemma cvec_mxZ (c : R) x : cvec_mx (c *: x) = c%:C *: cvec_mx x.
Proof. by rewrite -[RHS]cmxvecK cmxvecZ cvec_mxK. Qed.

End complex_mx2vec.

(* TODO: please pack mnorm later, perhaps an alias of matrix?     *)
(* equivalent norms : mnorm (complex matrix) <--> `|real vector| *)
Section complex_mx2vec_vnorm.
Variable (R: realType) (m n : nat).
Local Notation C := R[i].
Local Notation M := 'M[C]_(m.+1,n.+1).
Variable (mnorm : vnorm [lmodType C of M]).

Definition cm2rvnorm x := Re (mnorm (cvec_mx x)).
(* relation of cm2rvnorm and mnorm *)
Lemma cm2rvnormE x : mnorm x = (cm2rvnorm (cmxvec x))%:C.
Proof. rewrite /cm2rvnorm cmxvecK RRe_real//. apply/Num.Theory.ger0_real/normv_ge0. Qed.

Local Lemma hv1 : forall x y, cm2rvnorm (x + y) <= cm2rvnorm x + cm2rvnorm y.
Proof.
move=>x y. rewrite /cm2rvnorm -raddfD/= raddfD/=. 
move: (lev_norm_add mnorm (cvec_mx x) (cvec_mx y)).
by rewrite lecE=>/andP[_].
Qed.

Local Lemma hv2 : forall x, cm2rvnorm x = 0 -> x = 0.
Proof.
move=>x. rewrite /cm2rvnorm -{2}(cvec_mxK x). move/(f_equal (real_complex R)).
rewrite RRe_real. move/normv0_eq0=>->. apply: raddf0.
apply/Num.Theory.ger0_real/normv_ge0.
Qed.

Local Lemma hv4 : forall a x, cm2rvnorm (a *: x) = `|a| * cm2rvnorm x.
Proof.
move=>a x; rewrite /cm2rvnorm cvec_mxZ normvZ. set y := mnorm (cvec_mx x).
suff ->: `|a%:C| = `|a|%:C by destruct y; simpc=>/=.
by rewrite normc_def/= expr0n/= addr0 Num.Theory.sqrtr_sqr.
Qed.

Canonical cm2rvVnorm := Vnorm hv1 hv2 hv4.

Lemma ubound1 : exists2 c, 0 < c & forall x, mnorm x <= (c * `|cmxvec x|)%:C.
Proof.
move: (mnorm_ubounded cm2rvVnorm)=>[c [cgt0 Pc]].
exists c=>// x. rewrite cm2rvnormE lecR. apply Pc.
Qed.

Lemma lbound1 : exists2 c : R, 0 < c & forall x : 'M[C]_(m.+1,n.+1), (c * `|cmxvec x|)%:C <= mnorm x.
Proof.
move: (mnorm_lbounded cm2rvVnorm)=>[c [cgt0 Pc]].
exists c=>// x. rewrite cm2rvnormE lecR. apply Pc.
Qed.

End complex_mx2vec_vnorm.


(* equivalent norms : mnorm (complex matrix) <--> `|complex matrix| *)
(* `| | default norm, i.e., the maximum norm                        *)
(* thus prove the equivalence between mx_norm and any vector norm   *)
(* i.e., exists c1 c2, c1 > 0 & c2 > 0 &                            *)
(*                forall x, c1 * `|x| <= mnorm x <= c2 * `|x|       *)
(* then shows that the cauchy seq w.r.t. mnorm converge             *)
Section vnorm_eq_mx_norm.
Import realTypeMxCvg Num.Theory.
Local Open Scope complex_scope.
Variable (R: realType) (m n : nat).
Local Notation C := R[i].
Local Notation M := 'M[C]_(m.+1,n.+1).
Variable (mnorm : vnorm [lmodType C of M]).

Lemma hn1: forall (x y : M), `| x + y | <= `| x | + `| y |.
Proof. by apply: ler_norm_add. Qed.
Lemma hn2: forall (x : M), `| x | = 0 -> x = 0.
Proof. by apply: normr0_eq0. Qed.
Lemma hn4: forall a (x : M), `| a *: x | = `|a| * `| x |.
Proof. by move=>x a; rewrite normmZ. Qed.
Definition matrix_normedVnorm := Vnorm hn1 hn2 hn4.

Lemma mulcR (x y : R) : (x * y)%:C = x%:C * y%:C.
Proof. by simpc. Qed.

Lemma cmxnorm_ubounded : exists2 c, 0 < c & forall x, mnorm x <= c * `| x |.
Proof.
move: (ubound1 mnorm)=>[c1 c1gt0 Pc1].
move: (lbound1 matrix_normedVnorm)=>[c2 c2gt0 Pc2].
have Pc12 : 0 < (c1 / c2)%:C by rewrite ltcR; apply divr_gt0.
exists (c1 / c2)%:C => // x. 
apply (le_trans (Pc1 x)).
rewrite [_ * `|x|]mulrC -ler_pdivr_mulr//.
apply: (le_trans _ (Pc2 x)).
rewrite ler_pdivr_mulr// -mulcR lecR [_ * (_ / _)]mulrC !mulrA.
apply ler_pmul=>//. by apply ltW. 
by rewrite -ler_pdivr_mulr.
Qed.

Lemma cmxnorm_lbounded : exists2 c, 0 < c & forall x, c * `| x | <= mnorm x.
Proof.
move: (lbound1 mnorm)=>[c1 c1gt0 Pc1].
move: (ubound1 matrix_normedVnorm)=>[c2 c2gt0 Pc2].
have Pc12 : 0 < (c1 / c2)%:C by rewrite ltcR; apply divr_gt0.
exists (c1 / c2)%:C => // x. 
apply: (le_trans _ (Pc1 x)).
rewrite mulrC -ler_pdivl_mulr//.
apply (le_trans (Pc2 x)).
rewrite ler_pdivl_mulr// -mulcR lecR mulrC mulrA.
apply ler_pmul=>//; rewrite mulrVK=>//. by apply/ltW. all: by apply/unitf_gt0.
Qed.

Definition cauchy_seq_cmxmnorm (f : nat -> M) := 
  forall e : C, 0 < e -> exists N : nat, 
    forall s t, (N <= s)%N -> (N <= t)%N -> mnorm (f s - f t) < e.

(* cauchy seq characterization *)
Lemma cmxcauchy_seq_eq (f : nat -> M) :
cauchy_seq_cmxmnorm f <-> cmxcauchy_seq f.
Proof. split.
move: cmxnorm_lbounded => [c Pc le_mn] P e Pe.
have Pec: 0 < (e * c) by apply mulr_gt0.
move: (P _ Pec)=>[N PN]. exists N=>s t Ps Pt.
move: (le_lt_trans (le_mn (f s - f t)) (PN s t Ps Pt)).
set x := `|f s - f t|.
by rewrite mulrC -subr_gt0 -mulrBl (pmulr_lgt0 _ Pc) subr_gt0.
move: cmxnorm_ubounded => [c Pc le_mn] P e Pe.
have Pec: 0 < (e / c) by apply divr_gt0.
move: (P (e/c) Pec )=>[N PN]. exists N=>s t Ps Pt.
apply: (le_lt_trans (le_mn (f s - f t))).
move: (PN s t Ps Pt).
set x := `|f s - f t|.
by rewrite ltr_pdivl_mulr// mulrC.
Qed.

Lemma cmxcauchy_seq_cvg (f : nat -> M) :
  cauchy_seq_cmxmnorm f <-> cvg f.
Proof. by rewrite cmxcauchy_seq_eq; apply: cmxcauchy_seqP. Qed.

End vnorm_eq_mx_norm.

Section CauchySeqVnorm.
Variable (R: realType) (m n : nat) (mnorm : vnorm [lmodType R[i] of 'M[R[i]]_(m,n)]).

Lemma cmxcauchy_seqv_cvg (f : nat -> 'M[R[i]]_(m,n)) :
  cauchy_seqv mnorm f <-> cvg f.
Proof.
case: m mnorm f=>[mnorm' f|m']; last case: n=>[mnorm' f|n' mnorm' f].
1,2: by rewrite !mx_dim0; split=>_; [apply: cmxcvg_cst | apply cauchy_seqv_cst].
by rewrite -(cmxcauchy_seq_cvg mnorm').
Qed.

End CauchySeqVnorm.

Section EquivalenceVnorm.
Variable (R: realType) (m n : nat).
Variable (mnorm1 mnorm2 : vnorm [lmodType R[i] of 'M[R[i]]_(m,n)]).

Lemma cmxnormv_bounded :
  exists2 c : R[i], 0 < c & forall x, mnorm1 x <= c * mnorm2 x.
Proof.
case: m mnorm1 mnorm2; clear m mnorm1 mnorm2. 2: case: n=>m.
1,2: by move=>mnorm1 mnorm2; exists 1=>//= x; rewrite !mx_dim0 !normv0 mulr0.
move=>p mnorm1 mnorm2; move: (cmxnorm_ubounded mnorm1)=>/=[c1 Pc1 P1].
move: (cmxnorm_lbounded mnorm2)=>/=[c2 Pc2 P2].
exists (c1 / c2)=>[|x]; first by apply Num.Theory.divr_gt0.
apply (le_trans (P1 x)). 
rewrite -mulrA Num.Theory.ler_pmul2l// Num.Theory.ler_pdivl_mull//.
Qed.

Lemma cmxcauchy_seqv_eq (f : nat -> 'M[R[i]]_(m,n)) :
  cauchy_seqv mnorm1 f <-> cauchy_seqv mnorm2 f.
Proof. by rewrite !cmxcauchy_seqv_cvg. Qed.

End EquivalenceVnorm.

Section cmvnorm_cvg.
Import realTypeMxCvg Num.Theory.
Local Open Scope complex_scope.
Variable (R: realType) (m n : nat).
Local Notation C := R[i].
Variable (mnorm : vnorm [lmodType C of 'M[C]_(m,n)]).

Lemma cmxnormv_continuous : continuous mnorm.
Proof.
case: m mnorm; clear m mnorm. 2: case: n; clear n=>n.
1,2: move=>mnorm;
suff ->: (mnorm : 'M_(_,_) -> C) = (fun=>mnorm 0) by apply: cst_continuous.
1,2: by apply/funext=>x; rewrite mx_dim0E.
move=>m mnorm x s/= /nbhs_ballP [/=e egt0 Pb]; apply/nbhs_ballP.
move: (cmxnorm_ubounded mnorm) => [c Pc le_mn].
exists (e / c)=>/=[|y Py/=]. by apply divr_gt0.
apply Pb. move: Py. rewrite mx_norm_ball /ball/=.
move=>P1; apply: (le_lt_trans (lev_dist_dist mnorm _ _)).
by apply: (le_lt_trans (le_mn _)); rewrite mulrC -ltr_pdivl_mulr.
Qed.

Lemma cmxcvg_normv (f : 'M[C]_(m,n) ^nat) (a: 'M[C]_(m,n)) : 
  f --> a -> (fun x=> mnorm (f x)) --> (mnorm a).
Proof. by apply: continuous_cvg; apply: cmxnormv_continuous. Qed.

Lemma is_cmxcvg_normv (f : 'M[C]_(m,n) ^nat) : cvg f -> cvg (mnorm \o f).
Proof. by have := cvgP _ (cmxcvg_normv _); apply. Qed.

Lemma cmxlim_normv (f : 'M[C]_(m,n) ^nat) : 
  cvg f -> lim (mnorm \o f) = mnorm (lim f).
Proof. by move=> ?; apply: cvg_lim => //; apply: cmxcvg_normv. Qed.

End cmvnorm_cvg.

Require Import cpo.

Section Bolzano_Weierstrass.
Variables (R: realType).
Local Notation C := R[i].
Import Num.Def Num.Theory.

Lemma nonincreasing_homo {d : unit} [T : porderType d] (c : nat -> T) :
  (forall n, c n >= c n.+1)%O -> {homo c : x y / (x <= y)%N >-> (y <= x)%O}.
Proof.
move=> cc x y /subnK => <-; elim: (y - x)%N => //= n ih.
by rewrite addSn; apply: (le_trans _ ih); apply: cc.
Qed.

Lemma R_bound_subcvg (f : nat -> R) (M : R) :
  (forall n, `|f n| <= M) -> exists (h: nat -> nat), 
    (forall n, (h n.+1 > h n)%N) /\ cvg (f \o h).
Proof.
move=>sb; pose Q n := forall m, (n <= m)%N -> (f m <= f n).
pose Esub := (exists h : nat -> nat,
(forall n : nat, (h n < h n.+1)%N) /\ (forall n : nat, Q (h n))).
move: (EM Esub)=>[[h [Ph1 Ph2]]|/non_exists_nseq[N P1]].
exists h; split=>//. apply: nonincreasing_is_cvg.
by apply/nonincreasing_homo=> n/=; apply/(Ph2 n (h n.+1))/ltnW/Ph1.
by exists (-M)=>n/=[m _] <-; move: (sb (h m)); rewrite ler_norml=>/andP[].
have P2 n: {m : nat | (n < m)%N /\ f (N + n)%N <= f (N + m)%N}.
apply/cid. move: (P1 _ (leq_addr n N)); rewrite/Q.
apply contra_notP; rewrite not_existsP notK=>IH m.
rewrite leq_eqVlt=>/orP[/eqP<-//|Pm].
have E1: (N < m)%N by apply/(leq_ltn_trans _ Pm)/leq_addr.
apply/ltW; rewrite -(subnKC (ltnW E1)) real_ltNge ?num_real//; apply/negP.
move: (IH (m-N)%N); rewrite -implyNE=>P2; apply P2; by rewrite ltn_subRL.
exists ((fun n=>N+n)%N \o (nseq_sig P2)); split.
move=>n; rewrite /comp ltn_add2l nseq_sigE.
by move: (projT2 (P2 (nseq_sig P2 n)))=>[+_].
apply: nondecreasing_is_cvg.
apply/chain_homo=>n; rewrite/comp nseq_sigE.
by move: (projT2 (P2 (nseq_sig P2 n)))=>[].
by exists M=>n/=[m _] <-; move: (sb (N + nseq_sig P2 m)%N); rewrite ler_norml=>/andP[].
Qed.

Lemma normc_ge_Im (x : R[i]) : `|complex.Im x|%:C <= `|x|.
Proof.
by case: x => a b; simpc; rewrite -sqrtr_sqr ler_wsqrtr // ler_addr sqr_ge0.
Qed.

Lemma C_bound_subcvg (f : nat -> C) (M : C) :
  (forall n, `|f n| <= M) -> exists (h: nat -> nat), 
    (forall n, (h n.+1 > h n)%N) /\ cvg (f \o h).
Proof.
move=>P1. have PM : (complex.Re M)%:C = M.
by apply/RRe_real/ger0_real; apply: (le_trans (normr_ge0 _) (P1 0%N)).
have P2 n : `|complex.Re (f n)| <= complex.Re M.
by rewrite -lecR; apply: (le_trans (normc_ge_Re _)); rewrite PM.
move: (R_bound_subcvg P2)=>[h1 [Ph1 cvg1]].
have P3 n : `|complex.Im ((f \o h1) n)| <= complex.Re M.
by rewrite -lecR; apply: (le_trans (normc_ge_Im _)); rewrite PM/=.
move: (R_bound_subcvg P3)=>[h2 [Ph2 cvg2]].
move: cvg1=>/cvg_subseqP/(_ _ Ph2)=>cvg1/=.
exists (h1\o h2); split; first by move=>n/=; apply nchain_mono.
rewrite -(cseq_split (f \o (h1 \o h2))). apply is_ccvgD.
apply/is_ccvg_mapV. exact: rc_continuous.
have ->: (complex.Re (R:=R) \o (f \o (h1 \o h2))) = 
((fun n : nat => complex.Re (f n)) \o h1) \o h2 by apply/funext=>i/=.
apply/cvg_ex; exists (lim ((fun n : nat => complex.Re (f n)) \o h1)); exact: cvg1.
apply/is_ccvg_mapV; [exact: ic_continuous | exact: cvg2].
Qed.

Lemma row_mx_norm (T : numDomainType) p m n (M1 : 'M[T]_(p.+1,m.+1)) (M2 : 'M[T]_(p.+1,n.+1)) :
  mx_norm (row_mx M1 M2) = maxr (mx_norm M1) (mx_norm M2).
Proof.
rewrite /mx_norm; apply/le_anti/andP; split.
rewrite (bigmax_eq_arg (ord0,ord0))// =>[|i _]; last by rewrite -num_le//=.
set i := [arg max_(i > (ord0, ord0))`|row_mx M1 M2 i.1 i.2|%:nng]%O : 'I_p.+1 * 'I_(m.+1 + n.+1).
case: i=>a b/=; rewrite -(splitK b); case: (fintype.split b)=>/= c;
rewrite ?row_mxEl ?row_mxEr num_le_maxr; apply/orP; [left|right];
rewrite -num_abs_le//; apply/bigmax_gerP; right;
by exists (a,c)=>//=; rewrite -num_le/= normr_id.
rewrite num_le_maxl; apply/andP; split;
rewrite (bigmax_eq_arg (ord0,ord0))// =>[|i _].
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

Lemma big_card1 T (idx : T) (op : Monoid.law idx) (I : finType) i0 (F : I -> T) :
  #|I| = 1%N -> \big[op/idx]_i F i = F i0.
Proof.
move=>Pi. suff: (fun=>true) =1 pred1 i0. by apply big_pred1.
by move=>i; rewrite/=; move/eqP/fintype1P: Pi=>[x Px]; rewrite !Px eqxx.
Qed.
Arguments big_card1 [T idx op I] i0 [F].

Lemma index_enum1 (I : finType) i0 :
  #|I| = 1%N -> index_enum I = [:: i0].
Proof.
move=>Pi. move: Pi {+}Pi=>/mem_card1[x Px] /eqP/fintype1P[y Py].
by rewrite/index_enum/= -fintype.enumT (fintype.eq_enum Px) fintype.enum1 !Py.
Qed.

Lemma max_card1 T (idx : T) (op : T -> T -> T) (I : finType) i0 (F : I -> T) :
  #|I| = 1%N -> \big[op/idx]_i F i = op (F i0) idx.
Proof. by move=>P1; rewrite unlock/= (index_enum1 i0). Qed.

Lemma mx_norm1 (T : numDomainType) (M : 'M[T]_1) :
  `|M| = `|M ord0 ord0|.
Proof.
rewrite {1}/normr/= mx_normE.
set i0 := (ord0,ord0) : 'I_1 * 'I_1.
have ->: \big[maxr/0%:nng]_i `|M i.1 i.2|%:nng = 
  maxr `|M i0.1 i0.2|%:nng 0%:nng.
  by apply: max_card1; rewrite card_prod card_ord mul1n.
by rewrite max_l -?num_le//=.
Qed.

Lemma rV1_bound_subcvg (f : nat -> 'rV[C]_1) (M : C) :
  (forall n, `|(f n)| <= M) -> exists (h: nat -> nat), 
    (forall n, (h n.+1 > h n)%N) /\ cvg (f \o h).
Proof.
move=>P. pose u i := f i 0 0.
have: forall n, `|u n| <= M by move=>n; move: (P n); rewrite mx_norm1.
move=>/C_bound_subcvg[h [Ph1 /cvg_ex/=[x /cvg_seqP Px]]].
exists h; split=>//. set xm := (\matrix_(i,j) x : 'M[C]_1).
apply/cvg_ex; exists xm; suff: f \o h --> xm by [].
apply/cmxcvg_seqP =>e egt0; move: (Px _ egt0)=>[N PN].
by exists N=>i /PN; rewrite mx_normEV mx_norm1 !mxE.
Qed.

Lemma castmx_norm (T : numDomainType) m n m' n' (eqmn : (m = m') * (n = n')) 
  (M : 'M[T]_(m,n)) : mx_norm (castmx eqmn M) = mx_norm M.
Proof. by case: eqmn=>eqm eqn; case: m'/eqm; case: n'/eqn; rewrite castmx_id. Qed.

Lemma rV_bound_subcvg  (m : nat) (f : nat -> 'rV[C]_m.+1) (M : C) :
  (forall n, `|(f n)| <= M) -> exists (h: nat -> nat), 
    (forall n, (h n.+1 > h n)%N) /\ cvg (f \o h).
elim: m f =>[f|m IH f bf]. exact: rV1_bound_subcvg.
pose fl n := lsubmx (castmx (erefl, esym (addn1 m.+1)) (f n)).
pose fr n := rsubmx (castmx (erefl, esym (addn1 m.+1)) (f n)).
have cf n : f n = castmx (erefl, (addn1 m.+1)) (row_mx (fl n) (fr n))
 by rewrite /fl/fr hsubmxK castmx_comp castmx_id.
suff bfl n : `|fl n| <= M. suff bfr n : `|fr n| <= M.
2,3: move: (bf n); rewrite /normr/= cf castmx_norm row_mx_norm.
2,3: by rewrite num_le_maxl=>/andP[].
move: (IH _ bfl)=>[hl [hl1 /cmxcvg_seqP hl2]].
have bfr' n : `|(fr \o hl) n| <= M by rewrite/=.
move: (rV1_bound_subcvg bfr')=>[hr [hr1 /cmxcvg_seqP hr2]].
exists (hl \o hr); split; first by move=>n/=; apply nchain_mono.
pose lm := (castmx (erefl, (addn1 m.+1)) 
(row_mx (lim (fl \o hl)) (lim ((fr \o hl) \o hr)))).
apply/cvg_ex; exists lm; suff: (f \o (hl \o hr)) --> lm by [].
apply/cmxcvg_seqP=>e egt0. move: (hl2 _ egt0) (hr2 _ egt0)=>[N1 P1] [N2 P2].
set N := maxn N1 N2. exists N=>i Pi.
rewrite/= /lm cf -linearB /normr/= castmx_norm opp_row_mx add_row_mx 
  row_mx_norm num_lt_maxl -!mx_normE; apply/andP; split.
by apply/P1/(leq_trans _ (nchain_ge hr1 i))/(leq_trans _ Pi)/leq_maxl.
apply/P2/(leq_trans _ Pi)/leq_maxr.
Qed.

Lemma cmx_Bolzano_Weierstrass  (m n : nat) (f : nat -> 'M[C]_(m,n)) (M : C) :
  (forall n, mx_norm (f n) <= M) -> exists (h: nat -> nat), 
    (forall n, (h n.+1 > h n)%N) /\ cvg (f \o h).
Proof.
case: m f. move=>f _; exists id; split=>//; exact: is_cmxcvg_dim0n.
case: n. move=>n f _; exists id; split=>//; exact: is_cmxcvg_dimn0.
move=>n m f P1.
have P2 i : `|(mxvec \o f) i| <= M.
by rewrite/= -mxvec_norm /normr/=.
move: (rV_bound_subcvg P2)=>[h [P3 P4]].
exists h; split=>//. have ->: f \o h = vec_mx \o ((mxvec \o f) \o h).
by apply/funext=>i; rewrite/= mxvecK.
apply/is_cmxcvg_mapV. exact: vec_mx_continuous. exact: P4.
Qed.

(* bounded seq: cvg <-> any cvg subseq to a *)
Lemma ccvg_subseqP_cvg (m n : nat) (f : nat -> 'M[C]_(m,n)) (a : 'M[C]_(m,n)) (M : C): 
  (forall n, mx_norm (f n) <= M) ->
  f --> a <-> (forall (h: nat -> nat), (forall n, (h n.+1 > h n)%N) 
    -> cvg (f \o h) -> lim (f \o h) = a).
split.
move=>/cmxcvg_subseqP + h Ph _. move=>/(_ h Ph).
apply: cvg_lim. apply Cmxhausdorff.
move=>P. apply contrapT. rewrite cmxcvg_subseqPN.
rewrite -forallNP=> e. rewrite -forallNP=> h.
rewrite -!implyNE=>Ph Pe Pc.
have P1: forall n0 : nat, mx_norm ((f \o h) n0) <= M by move=>n0; apply H.
move: (cmx_Bolzano_Weierstrass P1)=>[h' [Ph']]. rewrite -compA=>Pc'.
have P2: ~ ((f \o (h \o h')) --> a).
rewrite cmxcvg_subseqPN; exists e; exists id; do 2 split=>//.
move=>n'; apply Pc.
apply P2. rewrite cmxcvg_limE; split=>[|//].
apply P=>[|//]. move=>n'/=. by apply nchain_mono.
Qed.

End Bolzano_Weierstrass.

(* TODO :                                                                   *)
(* 1. pack the vporder (vector preorder)                                    *)
(* 2. pack closed vporder, i.e., closed [set x : M | 0 ⊑ x ]                *)
(* Q: maybe is better to do everything in vect k? since 'M[C] is canonical  *)
(*   to vect C; but need to deal with trivial vector space (0-dim)          *)
(* it's better to redefine nosimpl of cvg and lim after packing things, in  *)
(* order to prevent searching the canonical structure which is much slower  *)
(* *** This section works for any matrix, even it is trivial                *)

(* TODO : norm is never used; please clean the code *)
Module CmxNormCvg.

Section Definitions.
Variables (R: realType) (m n : nat) (B : POrder.class_of 'M[R[i]]_(m,n)) (disp: unit).

Local Notation M := 'M[R[i]]_(m,n).
Local Notation "x '⊏' y" := (@Order.lt disp (@POrder.Pack disp M B) x y) 
  (at level 70, y at next level).
Local Notation "x '⊑' y" := (@Order.le disp (@POrder.Pack disp M B) x y) 
  (at level 70, y at next level).

Structure cmxnormcvg := Cmxnormcvg {
  mnorm : vnorm [lmodType R[i] of M];
  _ : forall (z x y : M), x ⊑ y -> x + z ⊑ y + z;
  _ : forall (e : R[i]) (x y : M), 0 < e -> x ⊑ y -> e *: x ⊑ e *: y;
  _ : closed [set x : M | (0 : M) ⊑ x];
  (* _ : forall (x y : M), (0 : M) ⊑ x -> (0 : M) ⊑ y 
        -> mnorm x + mnorm y = mnorm (x + y); *)
}.
Local Coercion mnorm : cmxnormcvg >-> vnorm.

Let op_id (op1 op2 : vnorm [lmodType R[i] of M]) := phant_id op1 op2.

Definition clone_vnormcvg op :=
  fun (opL : cmxnormcvg) & op_id opL op =>
  fun opd opz opc optr (opL' := @Cmxnormcvg op opd opz opc optr)
    & phant_id opL' opL => opL'.

End Definitions.

Module Import Exports.
Coercion mnorm : cmxnormcvg >-> vnorm.
Notation "[ 'cmxnormcvg' 'of' f ]" := (@clone_vnormcvg _ _ _ _ _ f _ id _ _ _ _ id)
  (at level 0, format"[ 'cmxnormcvg'  'of'  f ]") : form_scope.
End Exports.

Module Theory.

Section Property.
Import realTypeMxCvg Num.Theory.
Local Open Scope complex_scope.
Variable (R: realType) (m n : nat).
Local Notation C := R[i].
Local Notation M := 'M[C]_(m,n).
Variable (B : POrder.class_of M) (disp: unit).
Variable (mxnorm : cmxnormcvg B disp).

Local Notation "x '⊏' y" := (@Order.lt disp (@POrder.Pack disp M B) x y) (at level 70, y at next level).
Local Notation "x '⊑' y" := (@Order.le disp (@POrder.Pack disp M B) x y) (at level 70, y at next level).
Notation "'ubounded_by' b f" := (forall i, f i ⊑ b) (at level 10, b, f at next level).
Notation "'lbounded_by' b f" := (forall i, b ⊑ f i) (at level 10, b, f at next level).
Notation "'cmxnondecreasing_seq' f" := ({homo f : n m / (n <= m)%nat >-> (n ⊑ m)})
  (at level 10).
Notation "'cmxnonincreasing_seq' f" := ({homo f : n m / (n <= m)%nat >-> (m ⊑ n)})
  (at level 10).

Lemma lecmx_add2r (z x y : M) : x ⊑ y -> x + z ⊑ y + z.
Proof. by move: z x y; case: mxnorm. Qed.
Lemma lecmx_pscale2lP (e : R[i]) (x y : M) : 0 < e -> x ⊑ y -> e *: x ⊑ e *: y.
Proof. by move: e x y; case: mxnorm. Qed.
Lemma lecmx_pscale2l: forall (e : R[i]) (x y : M), 0 < e -> x ⊑ y = (e *: x ⊑ e *: y).
Proof. 
move=> e x y egt0. apply/Bool.eq_true_iff_eq.
split. by apply lecmx_pscale2lP. rewrite -{2}(scale1r x) -{2}(scale1r y) -(@mulVf _ e).
rewrite -!scalerA. apply lecmx_pscale2lP. rewrite invr_gt0//. by apply/lt0r_neq0.
Qed.
Lemma closed_gecmx0: closed [set x : M | (0 : M) ⊑ x].
Proof. by case: mxnorm. Qed.

Implicit Type (u v : M^nat).

Lemma subcmx_ge0 (x y : M) : ((0 : M) ⊑ x - y) = (y ⊑ x).
Proof. 
apply/Bool.eq_iff_eq_true; split=>[/(@lecmx_add2r y)|/(@lecmx_add2r (-y))];
by rewrite ?addrNK ?add0r// addrN.
Qed.

Lemma lecmx_opp2 : {mono (-%R : M -> M) : x y /~ x ⊑ y }.
Proof. by move=>x y; rewrite -subcmx_ge0 opprK addrC subcmx_ge0. Qed.

Lemma cmxnondecreasing_opp u :
  cmxnondecreasing_seq (- u) = cmxnonincreasing_seq u.
Proof. by rewrite propeqE; split => du x y /du; rewrite lecmx_opp2. Qed.

Lemma cmxnonincreasing_opp u :
  cmxnonincreasing_seq (- u) = cmxnondecreasing_seq u.
Proof. by rewrite propeqE; split => du x y /du; rewrite lecmx_opp2. Qed.

Lemma cmxlbounded_by_opp (b : M) u :
  lbounded_by (-b) (- u) = ubounded_by b u.
Proof. 
by rewrite propeqE; split => bu i; move: (bu i); 
  rewrite {2}/GRing.opp/= lecmx_opp2.
Qed.

Lemma cmxubounded_by_opp (b : M) u :
  ubounded_by (-b) (- u) = lbounded_by b u.
Proof. 
by rewrite propeqE; split => bu i; move: (bu i); 
  rewrite {2}/GRing.opp/= lecmx_opp2.
Qed.

(* following proof is quite difficult, prove it in future *)
(* unit sphere : compact ; [x | 0 ⊑ x] : closed *)
(* subclosed_compact: A := unit sphere `&` [x | 0 ⊑ x] -> compact A *)
(* A = empty : trivial case, 0 ⊑ x iff x = 0 ; only consider nontrivial case *)
(* convex hull B generated by A is compact https://en.wikipedia.org/wiki/Convex_hull *)
(* forall X : A, X ⊑ Y -> Y \in B or |Y| >= 1 *)
(* compact B -> compact C := mx_norm @` B *)
(* c := min C ; c > 0 & c <= 1 *)
(* 0 <= c <= 1 : since all x : C, 0 <= x <= 1 *)
(* c > 0 : if c = 0, then 0 \in B, 0 = \sum_i a_i *: x_i where 
  \sum_i a_i = 1 and a_i >= 0 & x_i \in A *)
(* at least one a_k > 0, 0 = a_k *: x_k + \sum_(i != k) a_i *: x_i *)
(* 0 ⊑ a_k *: x_k ⊑ a_k *: x_k + \sum_(i != k) a_i *: x_i = 0 *)
(* then a_k *: x_k = 0, contradiction since a_k > 0 and x_k != 0 *)
(* forall 0 ⊑ X ⊑ Y, c * mx_norm X <= mx_norm Y *)


(* different canonical route. prevent eq_op porderType ringType *)
Lemma ltcmx_def (x y : M) : (x ⊏ y) = (y != x) && (x ⊑ y).
Proof.
rewrite lt_def; congr (~~ _ && _); apply/Bool.eq_iff_eq_true.
split=>/eqP/=->; by rewrite eqxx.
Qed.

Lemma subcmx_gt0 (x y : M) : ((0 : M) ⊏ y - x) = (x ⊏ y).
Proof. by rewrite !ltcmx_def subcmx_ge0 subr_eq0. Qed.

Lemma cmxopen_nge0 : open [set x : M | ~ (0 : M) ⊑ x].
Proof. rewrite openC; apply closed_gecmx0. Qed.

Lemma cmxopen_nge y :  open [set x : M | ~ y ⊑ x].
Proof.
move: (@cmxaddr_continuous R m n (-y))=>/continuousP/=/(_ _ cmxopen_nge0).
suff ->: [set x : M | ~ y ⊑ x] = [set t | [set x | ~ (0 : M) ⊑ x] (- y + t)] by [].
by apply/funext=>x; rewrite /= addrC subcmx_ge0.
Qed.

Lemma cmxopen_nle0 : open [set x : M | ~ x ⊑ (0 : M)].
Proof.
move: (@cmxopp_continuous R m n)=>/continuousP/=/(_ _ cmxopen_nge0).
suff ->: [set x | ~ x ⊑ (0 : M)] = [set t | [set x | ~ (0 : M) ⊑ x] (- t)] by [].
by apply/funext=>x; rewrite /= -{2}oppr0 lecmx_opp2. 
Qed.

Lemma cmxopen_nle y :  open [set x : M | ~ x ⊑ y].
Proof.
move: (@cmxopp_continuous R m n)=>/continuousP/=/(_ _ (@cmxopen_nge (-y))).
suff ->: [set x : M | ~ x ⊑ y] = [set t | [set x : M | ~ - y ⊑ x] (- t)] by [].
by apply/funext=>x; rewrite /= lecmx_opp2.
Qed.

Lemma cmxclosed_ge (x : M) : closed [set y : M | x ⊑ y ].
Proof. 
set A := ~` [set y : M | ~ (x ⊑ y)].
have ->: (fun x0 : 'M_(m, n) => is_true (x ⊑ x0)) = A.
by rewrite predeqE /A => y/=; rewrite notK.
rewrite closedC. apply/cmxopen_nge. 
Qed.

Lemma cmxclosed_le (x : M) : closed [set y : M | y ⊑ x ].
Proof. 
set A := ~` [set y : M | ~ (y ⊑ x)].
have ->: (fun x0 : 'M_(m, n) => is_true (x0 ⊑ x)) = A.
by rewrite predeqE /A => y/=; rewrite notK.
rewrite closedC. apply/cmxopen_nle. 
Qed.

Lemma cmxlim_ge_near (x : M) (u : M ^nat) : 
  cvg u -> (\forall n \near \oo, x ⊑ u n) -> x ⊑ lim u.
Proof.
move=> /[swap] /(closed_cvg ((@Order.le disp (@POrder.Pack disp M B) x)))/= P1;
apply P1. apply: cmxclosed_ge.
Qed.

Lemma cmxlim_le_near (x : M) (u : M ^nat) : 
  cvg u -> (\forall n \near \oo, u n ⊑ x) -> lim u ⊑ x.
Proof.
move=> /[swap] /(closed_cvg (fun y =>(@Order.le disp (@POrder.Pack disp M B) y x)))/= P1;
apply P1. apply: cmxclosed_le.
Qed.

Lemma cmxler_lim_near (u_ v_ : M ^nat) : cvg u_ -> cvg v_ ->
  (\forall n \near \oo, u_ n ⊑ v_ n) -> lim u_ ⊑ lim v_.
Proof.
move=> uv cu cv; rewrite -(subcmx_ge0) -cmxlimB.
apply: cmxlim_ge_near. apply: is_cmxcvgB.
3: by apply: filterS cv => k; rewrite (subcmx_ge0).
1,3: by []. all: apply uv.
Qed.

Lemma cmxlim_ge (x : M) (u : M ^nat) : cvg u -> lbounded_by x u -> x ⊑ lim u.
Proof.
by move=>P1 P2; apply: (cmxlim_ge_near P1); apply: nearW.
Qed.

Lemma cmxlim_le (x : M) (u : M ^nat) : cvg u -> ubounded_by x u -> lim u ⊑ x.
Proof.
by move=>P1 P2; apply: (cmxlim_le_near P1); apply: nearW.
Qed.

Lemma ler_cmxlim (u v : M^nat) : cvg u -> cvg v ->
  (forall n, u n ⊑ v n) -> lim u ⊑ lim v.
Proof.
by move=>P1 P2 P3; apply: (cmxler_lim_near P1 P2); apply: nearW.
Qed.

Lemma cmxnondecreasing_cvg_le (u : M ^nat) :
       cmxnondecreasing_seq u -> cvg u -> ubounded_by (lim u) u.
Proof.
move=>Ph Pc i; apply: cmxlim_ge_near=>//; exists i=>// j; apply Ph.
Qed.

Lemma cmxnonincreasing_cvg_ge (u : M ^nat) : 
  cmxnonincreasing_seq u -> cvg u -> lbounded_by (lim u) u.
Proof.
move=>Ph Pc i; apply: cmxlim_le_near=>//; exists i=>// j; apply Ph.
Qed.

Lemma nchain_mono1 (h: nat -> nat) :
  (forall n, (h n.+1 > h n)%N) -> forall n m, (n <= m)%N -> (h n <= h m)%N.
Proof.
move=>P1 n' m'; rewrite leq_eqVlt=>/orP[/eqP->//|P2].
by apply/ltnW/nchain_mono.
Qed.

Lemma ha (X Y : M) a : ((0 : M) ⊑ X) && (X ⊑ Y) -> 0 < a < 1 ->
  ((0 : M) ⊑ a*:X) && (a*:X ⊑ Y).
Proof.
move=>/andP[P1 P2]/andP[P3]; rewrite -subr_gt0=>P4; apply/andP; split.
by move: (lecmx_pscale2lP P3 P1); rewrite scaler0.
apply: (le_trans (lecmx_pscale2lP P3 P2)).
move: (le_trans P1 P2)=>/(lecmx_pscale2lP P4).
by rewrite scaler0 scalerBl scale1r=>/(lecmx_add2r (a*:Y)); rewrite addrNK add0r.
Qed.

Lemma hb (e : C) : 0 < e -> exists k, k.+1%:R^-1 < e.
Proof.
move=>egt0. have ->: e = (complex.Re e)%:C.
by case: e egt0=>/= x y; rewrite ltcE/==>/andP[]/eqP->.
have regt0 : 0 < (complex.Re e) by case: e egt0=>x y; rewrite ltcE/==>/andP[].
move/ltr_add_invr: regt0=>[k Pk]; exists k.
by rewrite -natrC -realcI ltcR; move: Pk; rewrite add0r.
Qed.

Lemma ler1Sn (T : numDomainType) i : 1 <= i.+1%:R :> T.
Proof. by rewrite -addn1 natrD ler_addr. Qed.

Lemma porder_mx_norm_bound (Y : M) : exists c, c > 0 /\ 
  (forall X, ((0 : M) ⊑ X) && (X ⊑ Y) -> c * mx_norm X <= mx_norm Y).
Proof.
case E: (Y == 0); first by move/eqP: E=>->; exists 1; split=>// x; 
  rewrite -eq_le=>/eqP<-; rewrite normv0 mulr0.
have Q1: mx_norm Y > 0 by rewrite normv_gt0 E.
pose c i := i.+1%:R * (1 + mx_norm Y).
have cinc i : c i >= 1 + mx_norm Y by rewrite/c ler_pmull ?addr_gt0// ler1Sn.
have Q2 i : c i > i.+1%:R by rewrite/c ltr_pmulr// ltr_addl.
have Q3 i : c i > 0 by rewrite /c mulr_gt0// addr_gt0.
have Q4 i : 0 < mx_norm Y / c i by rewrite divr_gt0.
rewrite not_existsP=>P1.
have P2 i: {X : M | ((0 : M) ⊑ X) && (X ⊑ Y) /\ (mx_norm X > c i)}.
apply/cid; move: (P1 (mx_norm Y/c i)); rewrite -implyNE=>/(_ (Q4 i)).
rewrite not_existsP; apply contra_not=>P2 x P3; move: (P2 x).
rewrite -implyNE=>/(_ P3)/negP; rewrite -mulrA ger_pmulr// ler_pdivr_mull// mulr1.
by rewrite real_leNgt// ger0_real// ?normv_ge0//; apply/ltW.
pose x i := projT1 (P2 i).
have P7 i : ((0 : M) ⊑ x i) && (x i ⊑ Y) by move: (projT2 (P2 i))=>[].
have P4 i : c i < mx_norm (x i) by move: (projT2 (P2 i))=>[].
have P5 i : 0 < mx_norm (x i) by apply: (lt_trans _ (P4 _)).
pose nx i := (mx_norm (x i))^-1 *: (x i).
have norm_nx i : mx_norm (nx i) = 1.
by rewrite /nx normvZ/= gtr0_norm ?mulVf// ?invr_gt0//; apply: lt0r_neq0.
have bound_nx i : mx_norm (nx i) <= 1 by rewrite norm_nx.
move: (cmx_Bolzano_Weierstrass bound_nx)=>[h [mn]].
move: (nchain_ge mn)=>hgen.
set y := nx \o h=>Cy; pose ly := lim y : M.
have cy : y --> ly by [].
have P3 i : ((0 : M) ⊑ y i) && (y i ⊑ Y).
rewrite /y/=/nx; apply/ha=>//.
rewrite invr_gt0 invf_lt1// P5/=; apply: (lt_trans _ (P4 _)).
apply: (le_lt_trans _ (Q2 _)); by rewrite -addn1 natrD ler_addr.
have ly_ge0: ((0 : M) ⊑ ly) by apply: cmxlim_ge=>[//|i]; move: (P3 i)=>/andP[].
have Q5 i: mx_norm (Y - x i) > i.+1%:R.
rewrite addrC; move: (lev_sub_norm_add mx_norm_vnorm (- x i) Y)=>/=.
apply: lt_le_trans; rewrite mx_normN ltr_subr_addl.
apply: (le_lt_trans _ (P4 _)); rewrite addrC/c mulrDr.
by rewrite mulr1 ler_add2l ler_pmull// ler1Sn.
have Q6 i: mx_norm (Y - x i) > 0 by apply: (lt_trans _ (Q5 _)).
pose nnx i := (mx_norm (Y - x (h i)))^-1 *: (Y - x (h i)).
pose nnx1 i := (mx_norm (Y - x (h i)))^-1 *: Y.
pose nnx2 i := (mx_norm (Y - x (h i)))^-1 * mx_norm (x (h i)).
have: nnx --> 0 - 1 *: ly.
have ->: nnx = nnx1 - (fun i=>nnx2 i *: y i).
apply/funext=>i; rewrite/nnx/nnx1 {3}/GRing.add/={4}/GRing.opp/=/nnx2/nx.
by rewrite scalerA -mulrA mulfV ?mulr1 ?scalerBr// lt0r_neq0.
have Q7 e: 0 < e -> exists N : nat, forall i : nat, (N <= i)%N -> 
  mx_norm Y / (mx_norm (Y - x (h i))) < e.
  move=>egt0; have /hb: e / mx_norm Y > 0 by rewrite divr_gt0.
  move=>[k Pk]; exists k=>i Pi; rewrite/=mulrC -ltr_pdivl_mulr//; apply: (le_lt_trans _ Pk).
  rewrite lef_pinv ?posrE//; apply/ltW; apply: (le_lt_trans _ (Q5 _)).
  by rewrite ler_nat ltnS; apply: (leq_trans Pi).
apply cmxcvgB. 2: apply cmxcvgZ=>[|//].
apply/cmxcvg_seqP=>e egt0; move: (Q7 e egt0)=>[k Pk]; exists k=>i/Pk.
by rewrite add0r mx_normN/nnx1 normvZ/= gtr0_norm ?invr_gt0// mulrC.
apply ccvg_seqP=>e egt0; move: (Q7 e egt0)=>[k Pk]; exists k=>i/Pk.
rewrite ltr_pdivr_mulr// =>P6.
rewrite/nnx2 -(@mulfV _ (mx_norm (Y - x (h i))) _); last by apply/lt0r_neq0.
rewrite mulrC -mulrBr normrM gtr0_norm ?ltr_pdivr_mull// ?invr_gt0// mulrC.
apply: (le_lt_trans _ P6); rewrite -[mx_norm (x (h i))]normvN/= 
  -{2}[Y](addrNK (x (h i))) -{4}(opprK (x (h i))); apply: lev_dist_dist.
rewrite scale1r add0r=>cny. have Cny: cvg nnx by apply/cvg_ex; exists (-ly). 
have nly_ge0: ((0 : M) ⊑ - ly). rewrite -(cvg_lim _ cny); last by apply Cmxhausdorff.
apply: cmxlim_ge=>[//|i].
suff: ((0 : M) ⊑ nnx i) && (nnx i ⊑ Y) by move=>/andP[].
rewrite /nnx; apply/ha; apply/andP; split.
rewrite subcmx_ge0. 2: rewrite -subcmx_ge0 opprB addrC addrNK.
1,2: by move: (P7 (h i))=>/andP[].
rewrite invr_gt0//. rewrite invf_lt1//; apply/(le_lt_trans _ (Q5 _))/ler1Sn.
have : mx_norm ly = 1.
rewrite -(cmxlim_normv (mx_norm_vnorm) Cy)=>/=.
suff ->: mx_norm (n:=n) \o y = fun=>1 by apply/lim_cst/Chausdorff.
by apply/funext=>i; rewrite/=/y//=.
have: ((0 : M) ⊑ ly) && (ly ⊑ 0) by rewrite ly_ge0/= -subcmx_ge0 add0r.
by rewrite -eq_le eq_sym=>/eqP->/eqP; rewrite normv0 eq_sym oner_eq0.
Qed.

Lemma lubounded_cmxnorm (bl br : M) u :
  lbounded_by bl u -> ubounded_by br u -> 
  exists c : C, forall n, mx_norm (u n) <= c.
Proof.
move: (porder_mx_norm_bound (br-bl))=>[c [Pc P]] Pl Pr.
exists (mx_norm (br - bl) / c + mx_norm bl)=>i.
rewrite -[u i](addrNK bl). apply: (le_trans (ler_mx_norm_add _ _)).
rewrite ler_add2r ler_pdivl_mulr// mulrC P//; apply/andP; split.
by rewrite subcmx_ge0. by apply lecmx_add2r.
Qed.

Lemma cmxnondecreasing_is_cvg (f : nat -> M) (b : M) :
  cmxnondecreasing_seq f -> ubounded_by b f -> cvg f.
move=>P1 P2.
have P3: lbounded_by (f 0%N) f by move=>i; by apply/P1.
move: (lubounded_cmxnorm P3 P2)=>[c Pc].
move: (cmx_Bolzano_Weierstrass Pc)=>[h0 [Ph0 cvgh0]].
apply/cvg_ex. exists (lim (f \o h0)).
apply/(ccvg_subseqP_cvg (lim (f \o h0)) Pc)=>h1 Ph1 cvgh1.
suff: (lim (f \o h1) ⊑ lim (f \o h0)) && (lim (f \o h0) ⊑ lim (f \o h1)).
by rewrite -eq_le=>/eqP.
apply/andP; split; apply: (cmxlim_le)=>[|i].
2: have P4: (f \o h1) i ⊑ (f \o h0) (h1 i) by apply/P1/nchain_ge.
4: have P4: (f \o h0) i ⊑ (f \o h1) (h0 i) by apply/P1/nchain_ge.
2,4: apply: (le_trans P4 _); apply (cmxnondecreasing_cvg_le).
1,5: apply cvgh1. 2,4: apply cvgh0.
all: by move=>x y Pxy; apply P1; apply/nchain_mono1.
Qed.

Lemma cmxnonincreasing_is_cvg (f : nat -> M) (b : M) :
    cmxnonincreasing_seq f -> lbounded_by b f -> cvg f.
Proof.
rewrite -(cmxnondecreasing_opp) -(cmxubounded_by_opp) -is_cmxcvgNE.
exact: cmxnondecreasing_is_cvg.
Qed.

End Property.

End Theory.
Include Theory.

End CmxNormCvg.
Import CmxNormCvg.Exports.

Import CmxNormCvg.

(* FinNormedModType *)
(* VOrderFinNormedModType *)
Module FinNormedModule.

Section ClassDef.

Variable R : realType.

Record class_of (T : Type) := Class {
  base : NormedModule.class_of [numDomainType of R[i]] T ;
  mixin : Vector.mixin_of (GRing.Lmodule.Pack _ base);
}.
Local Coercion base : class_of >-> NormedModule.class_of.
Definition base2 T (cT : class_of T) := @Vector.Class _ _ (@base T cT) (@mixin T cT).
Local Coercion base2 : class_of >-> Vector.class_of.

Structure type (phR : phant R[i]) := Pack { sort; _ : class_of sort }.
Local Coercion sort : type >-> Sortclass.

Variables (phR : phant R[i]) (T : Type) (cT : type phR).
Definition class := let: Pack _ c  as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack phR T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack :=
  fun bT (b : NormedModule.class_of _ T) & phant_id (@NormedModule.class _ (Phant R[i]) bT) b =>
  fun mT m & phant_id (@Vector.class _ (Phant R[i]) mT) (@Vector.Class _ T b m) =>
    @Pack phR T (@Class T b m).

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition zmodType := @GRing.Zmodule.Pack cT xclass.
Definition normedZmodType := @Num.NormedZmodule.Pack _ phR cT xclass.
Definition lmodType := @GRing.Lmodule.Pack _ phR cT xclass.
Definition pointedType := @Pointed.Pack cT xclass.
Definition filteredType := @Filtered.Pack cT cT xclass.
Definition topologicalType := @Topological.Pack cT xclass.
Definition uniformType := @Uniform.Pack cT xclass.
Definition pseudoMetricType := @PseudoMetric.Pack _ cT xclass.
Definition pseudoMetricNormedZmodType :=
  @PseudoMetricNormedZmodule.Pack _ phR cT xclass.
Definition normedModType := @NormedModule.Pack _ phR cT xclass.
Definition vectType := @Vector.Pack _ phR cT xclass.
Definition normedMod_zmodType := @GRing.Zmodule.Pack normedModType xclass.
Definition normedMod_lmodType := @GRing.Lmodule.Pack _ phR normedModType xclass.
Definition normedMod_vectType := @Vector.Pack _ phR normedModType xclass.

End ClassDef.

Module Import Exports.
Coercion base : class_of >-> NormedModule.class_of.
Coercion base2 : class_of >-> Vector.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion pseudoMetricNormedZmodType : type >-> PseudoMetricNormedZmodule.type.
Canonical pseudoMetricNormedZmodType.
Coercion normedZmodType : type >-> Num.NormedZmodule.type.
Canonical normedZmodType.
Coercion lmodType : type >-> GRing.Lmodule.type.
Canonical lmodType.
Coercion pointedType : type >-> Pointed.type.
Canonical pointedType.
Coercion filteredType : type >-> Filtered.type.
Canonical filteredType.
Coercion topologicalType : type >-> Topological.type.
Canonical topologicalType.
Coercion uniformType : type >-> Uniform.type.
Canonical uniformType.
Coercion pseudoMetricType : type >-> PseudoMetric.type.
Canonical pseudoMetricType.
Coercion normedModType : type >-> NormedModule.type.
Canonical normedModType.
Coercion vectType : type >-> Vector.type.
Canonical vectType.
Canonical normedMod_zmodType.
Canonical normedMod_lmodType.
Canonical normedMod_vectType.
Notation finNormedModType R := (type (Phant R)).
Notation FinNormedModType R T := (@pack _ (Phant R) T _ _ id _ _ id).
Notation "[ 'finNormedModType' R 'of' T 'for' cT ]" :=  (@clone _ (Phant R) T cT _ idfun)
  (at level 0, format "[ 'finNormedModType'  R  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'finNormedModType' R 'of' T ]" :=  (@clone _ (Phant R) T _ _ id)
  (at level 0, format "[ 'finNormedModType'  R  'of'  T ]") : form_scope.
End Exports.

End FinNormedModule.

Import FinNormedModule.Exports.

Canonical C_regular_finNormedModType (R : realType) := 
  Eval hnf in (FinNormedModType R[i] R[i]^o).
Canonical C_finNormedModType (R : realType) :=
  Eval hnf in [finNormedModType R[i] of R[i] for [finNormedModType R[i] of R[i]^o]].

Module VOrderFinNormedModule.

Section ClassDef.

Record mixin_of (R : realType) (V : finNormedModType R[i])
  (Rorder : POrder.mixin_of (Equality.class V))
  (le_op := POrder.le Rorder)
  := Mixin {
  _ : closed [set x : V | (le_op 0 x)] ;
}.

Variable R : realType.

Record class_of (T : Type) := Class {
  base : FinNormedModule.class_of R T;
  order_mixin : POrder.mixin_of (Equality.class (FinNormedModule.Pack _ base));
  vorder_mixin : VOrder.mixin_of order_mixin;
  mixin : mixin_of order_mixin;
}.
Local Coercion base : class_of >-> FinNormedModule.class_of.
Definition vorder_base T (cT : class_of T) :=
  @VOrder.Class _ _ (@base T cT) (order_mixin cT) (vorder_mixin cT).
Local Coercion vorder_base : class_of >-> VOrder.class_of.

Structure type (phR : phant R[i]) := Pack { sort; _ : class_of sort }.
Local Coercion sort : type >-> Sortclass.

Variables (phR : phant R[i]) (T : Type) (cT : type phR).
Definition class := let: Pack _ c  as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack phR T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack (b0 : FinNormedModule.class_of R T)
           (om0 : POrder.mixin_of (Equality.class (FinNormedModule.Pack (Phant R[i]) b0)))
           (m0 : @mixin_of R (@FinNormedModule.Pack R (Phant R[i]) T b0) om0) :=
  fun bT (b : FinNormedModule.class_of R T)
      & phant_id (@FinNormedModule.class R (Phant R[i]) bT) b =>
  fun om & phant_id om0 om =>
  fun vmT vm & phant_id (@VOrder.class _ (Phant R[i]) vmT) (@VOrder.Class _ T b om vm) =>
  fun m & phant_id m0 m =>
  @Pack phR T (@Class T b om vm m).

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition zmodType := @GRing.Zmodule.Pack cT xclass.
Definition normedZmodType := @Num.NormedZmodule.Pack _ phR cT xclass.
Definition lmodType := @GRing.Lmodule.Pack _ phR cT xclass.
Definition pointedType := @Pointed.Pack cT xclass.
Definition filteredType := @Filtered.Pack cT cT xclass.
Definition topologicalType := @Topological.Pack cT xclass.
Definition uniformType := @Uniform.Pack cT xclass.
Definition pseudoMetricType := @PseudoMetric.Pack _ cT xclass.
Definition pseudoMetricNormedZmodType :=
  @PseudoMetricNormedZmodule.Pack _ phR cT xclass.
Definition normedModType := @NormedModule.Pack _ phR cT xclass.
Definition finNormedModType := @FinNormedModule.Pack _ phR cT xclass.
Definition vectType := @Vector.Pack _ phR cT xclass.
Definition porderType := @POrder.Pack vorder_display cT xclass.
Definition vorderType := @VOrder.Pack _ phR cT xclass.
Definition finNormedMod_zmodType := @GRing.Zmodule.Pack finNormedModType xclass.
Definition finNormedMod_lmodType := @GRing.Lmodule.Pack _ phR finNormedModType xclass.
Definition finNormedMod_vectType := @Vector.Pack _ phR finNormedModType xclass.
Definition finNormedMod_porderType := @POrder.Pack vorder_display finNormedModType xclass.
Definition finNormedMod_vorderType := @VOrder.Pack _ phR finNormedModType xclass.

End ClassDef.

Module Import Exports.
Coercion base : class_of >-> FinNormedModule.class_of.
Coercion vorder_base : class_of >-> VOrder.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion pseudoMetricNormedZmodType : type >-> PseudoMetricNormedZmodule.type.
Canonical pseudoMetricNormedZmodType.
Coercion normedZmodType : type >-> Num.NormedZmodule.type.
Canonical normedZmodType.
Coercion lmodType : type >-> GRing.Lmodule.type.
Canonical lmodType.
Coercion pointedType : type >-> Pointed.type.
Canonical pointedType.
Coercion filteredType : type >-> Filtered.type.
Canonical filteredType.
Coercion topologicalType : type >-> Topological.type.
Canonical topologicalType.
Coercion uniformType : type >-> Uniform.type.
Canonical uniformType.
Coercion pseudoMetricType : type >-> PseudoMetric.type.
Canonical pseudoMetricType.
Coercion normedModType : type >-> NormedModule.type.
Canonical normedModType.
Coercion finNormedModType : type >-> FinNormedModule.type.
Canonical finNormedModType.
Coercion vectType : type >-> Vector.type.
Canonical vectType.
Coercion porderType : type >-> POrder.type.
Canonical porderType.
Coercion vorderType : type >-> VOrder.type.
Canonical vorderType.
Canonical finNormedMod_zmodType.
Canonical finNormedMod_lmodType.
Canonical finNormedMod_vectType.
Canonical finNormedMod_porderType.
Canonical finNormedMod_vorderType.
Notation vorderFinNormedModType R := (type (Phant R)).
Notation VOrderFinNormedModType R T m := 
  (@pack _ (Phant R) T _ _ m _ _ id _ id _ _ id _ id).
Notation VOrderFinNormedModMixin := Mixin.
Notation "[ 'vorderFinNormedModType' R 'of' T 'for' cT ]" := (@clone _ (Phant R) T cT _ idfun)
  (at level 0, format "[ 'vorderFinNormedModType'  R  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'vorderFinNormedModType' R 'of' T ]" := (@clone _ (Phant R) T _ _ id)
  (at level 0, format "[ 'vorderFinNormedModType'  R  'of'  T ]") : form_scope.
End Exports.

End VOrderFinNormedModule.

Import VOrderFinNormedModule.Exports.

Lemma continuous_comp_simp (R S T : topologicalType) (f : R -> S) (g : S -> T) :
  continuous f -> continuous g -> continuous (g \o f)%FUN.
Proof. 
move=>cf cg; suff: forall x, {for x, continuous (g \o f)%FUN} by [].
move=>x. apply continuous_comp. apply cf. apply cg.
Qed.

Section FinNormedModTypeComplete.
Variable (R : realType).
Local Notation C := R[i].
Import Vector.InternalTheory Num.Def Num.Theory.

Lemma bounded_normr_cmxnorm (V : normedModType C) 
  m n (f: V -> 'M[C]_(m,n)) (lf: linear f) (bf: bijective f) :
  (exists c, c > 0 /\ forall x : V, `|x| <= c * mx_norm (f x))
  /\ (exists c, c > 0 /\ forall x : V, mx_norm (f x) <= c * `|x|).
move: bf=>[g fK gK]; move: (can2_linearP lf fK gK)=>lg.
pose mn x := `|g x|.
have meq0 : forall x, mn x = 0 -> x = 0.
  by move=>x/normr0_eq0; rewrite -{2}(gK x)/==>->; rewrite (linearlfE lf) linear0.
have mtrg : forall x y, mn (x + y) <= mn x + mn y.
  by move=>x y; rewrite /mn (linearlfE lg) linearD ler_norm_add.
have mZ : forall (a: C) (x : 'M_(m,n)), mn (a *: x) = `|a| * mn x.
  by move=>a x; rewrite /mn (linearlfE lg) linearZ normmZ.
pose mvn := Vnorm mtrg meq0 mZ.
have x2m : forall x, `|x| = mn (f x) by move=>x; rewrite /mn fK.
split.
move: (cmxnormv_bounded mvn (@mx_norm_vnorm _ _ _))=>[c /= cgt0 Pml].
exists c; split=>// x. by rewrite x2m.
move: (cmxnormv_bounded (@mx_norm_vnorm _ _ _) mvn)=>[c /= cgt0 Pml].
exists c; split=>// x. by rewrite x2m.
Qed.

Lemma bounded_cmxnorm_normr (V : normedModType C) 
  (m n: nat) (g: 'M[C]_(m,n) -> V) (lg: linear g) (bg: bijective g) :
  (exists c, c > 0 /\ forall x : 'M[C]_(m,n), mx_norm x <= c * `|g x|)
  /\ (exists c, c > 0 /\ forall x : 'M[C]_(m,n), `|g x| <= c * mx_norm x).
Proof.
move: bg=>[f gK fK]. move: (bounded_normr_cmxnorm (can2_linearP lg gK fK) 
  (can2_bij gK fK))=>[[c1 [c1gt0 Pc1]] [c2 [c2gt0 Pc2]]].
split. exists c2. split=>// x. by rewrite -{1}(gK x).
exists c1. split=>// x. by rewrite -{2}(gK x).
Qed.

Lemma bijective_to_cmx_continuous (V : normedModType C) 
  (m n: nat) (f: V -> 'M[C]_(m,n)) (lf: linear f) (bf: bijective f) :
  continuous f.
Proof.
case: m f lf bf=>[f _ _|]; last case: n=>[m f _ _|].
1,2: by rewrite mx_dim0=>x; apply: cst_continuous.
move=>m n f lf bf.
rewrite (linearlfE lf) -linear_bounded_continuous -bounded_funP=>r/=.
move: (bounded_normr_cmxnorm lf bf)=>[_ [c2 [c2gt0 Pc2]]].
exists (c2 * r)=>x. rewrite -(ler_pmul2l c2gt0) {2}/normr/=.
apply (le_trans (Pc2 _)).
Qed.

Lemma bijective_of_cmx_continuous (V : normedModType C) 
  (m n: nat) (g: 'M[C]_(m,n) -> V) (lg: linear g) (bg: bijective g) :
  continuous g.
Proof.
case: m g lg bg=>[g _ _|]; last case: n=>[m g _ _|].
1,2: have ->: g = (fun=>g 0) by apply/funext=>i; rewrite mx_dim0.
1,2: apply: cst_continuous.
move=>m n g lg bg.
rewrite (linearlfE lg) -linear_bounded_continuous -bounded_funP=>r/=.
move: (bounded_cmxnorm_normr lg bg)=>[_ [c2 [c2gt0 Pc2]]].
exists (c2 * r)=>x. rewrite -(ler_pmul2l c2gt0) {1}/normr/=.
apply (le_trans (Pc2 _)).
Qed.

Lemma bijective_to_cmx_cvgE (V : normedModType C) 
  (m n: nat) (f: V -> 'M[C]_(m,n)) (u : nat -> V) (a : V)
  (lf: linear f) (bf: bijective f) :
  u --> a = ((f \o u)%FUN --> f a).
Proof.
rewrite propeqE; split; last move: {+}bf=>[g fK gK].
by apply: continuous_cvg; apply/(bijective_to_cmx_continuous lf bf).
have P: u = (g \o (f \o u))%FUN by apply/funext=>i/=; rewrite fK.
have P1: a = g (f a) by rewrite fK. 
rewrite [in X in _ -> X]P [in X in _ -> X]P1; apply: continuous_cvg. 
apply (bijective_of_cmx_continuous (can2_linearP lf fK gK) (can2_bij fK gK)).
Qed.

Lemma bijective_of_cmx_cvgE (V : normedModType C) 
  (m n: nat) (f: 'M[C]_(m,n) -> V) (u : nat -> 'M[C]_(m,n)) (a : 'M[C]_(m,n))
  (lf: linear f) (bf: bijective f) :
  u --> a = ((f \o u)%FUN --> f a).
Proof.
rewrite propeqE; split; last move: {+}bf=>[g fK gK].
by apply: continuous_cvg; apply/(bijective_of_cmx_continuous lf bf).
have P: u = (g \o (f \o u))%FUN by apply/funext=>i/=; rewrite fK.
have P1: a = g (f a) by rewrite fK. 
rewrite [in X in _ -> X]P [in X in _ -> X]P1; apply: continuous_cvg. 
apply (bijective_to_cmx_continuous (can2_linearP lf fK gK) (can2_bij fK gK)).
Qed.

Lemma bijective_to_cmx_is_cvgE (V : normedModType C) 
  (m n: nat) (f: V -> 'M[C]_(m,n)) (u : nat -> V)
  (lf: linear f) (bf: bijective f) :
  cvg u = cvg (f \o u)%FUN.
Proof.
rewrite propeqE; split; last move: {+}bf=>[g fK gK].
move/cvg_ex=>[a Pa]. apply/cvg_ex. exists (f a). by rewrite -bijective_to_cmx_cvgE.
move/cvg_ex=>[a Pa]. apply/cvg_ex. exists (g a).
have P1: a = f (g a) by []. 
move: Pa. by rewrite [in X in X -> _]P1 -bijective_to_cmx_cvgE.
Qed.

Lemma bijective_of_cmx_is_cvgE (V : normedModType C) 
  (m n: nat) (f: 'M[C]_(m,n) -> V) (u : nat -> 'M[C]_(m,n))
  (lf: linear f) (bf: bijective f) :
  cvg u = cvg (f \o u)%FUN.
Proof.
rewrite propeqE; split; last move: {+}bf=>[g fK gK].
move/cvg_ex=>[a Pa]. apply/cvg_ex. exists (f a). by rewrite -bijective_of_cmx_cvgE.
move/cvg_ex=>[a Pa]. apply/cvg_ex. exists (g a).
have P1: a = f (g a) by []. 
move: Pa. by rewrite [in X in X -> _]P1 -bijective_of_cmx_cvgE.
Qed.

Lemma bijective_to_cmx_limE (V : normedModType C) 
  (m n: nat) (f: V -> 'M[C]_(m,n)) (u : nat -> V)
  (lf: linear f) (bf: bijective f) :
  cvg u -> lim (f \o u)%FUN = f (lim u).
Proof.
move=> ?; apply: cvg_lim; first by apply: Cmxhausdorff.
by rewrite -bijective_to_cmx_cvgE.
Qed.

Lemma bijective_of_cmx_limE (V : normedModType C) 
  (m n: nat) (f: 'M[C]_(m,n) -> V) (u : nat -> 'M[C]_(m,n))
  (lf: linear f) (bf: bijective f) :
  cvg u -> lim (f \o u)%FUN = f (lim u).
Proof.
move=> ?; apply: cvg_lim; first by apply: norm_hausdorff.
by rewrite -bijective_of_cmx_cvgE.
Qed.

Lemma V_complete_sub (V : normedModType C) (m n: nat) (f: V -> 'M[C]_(m,n)) (lf: linear f) (bf : bijective f)
  (F : set (set V)) :
  ProperFilter F -> cauchy F -> cvg F.
Proof.
move: bf=>[g fK gK]; move: (can2_linearP lf fK gK)=>lg.
move=> PF /cauchyP F_cauchy.
case Em: (m == m.-1.+1); [move/eqP:Em=>Em|]; last first.
2: case En: (n == n.-1.+1); [move/eqP:En=>En|]; last first.
- have P1: 0%N = m by move: Em; clear -m; case: m=>/=[|k']; [case: eqP|rewrite eqxx].
2:have P1: 0%N = n by move: En; clear -n; case: n=>/=[|k']; [case: eqP|rewrite eqxx].
1,2: apply/cvg_ex=>/=; exists 0; apply: (cvg_distW)=>/= e egt0;
     apply: filter_near_of => x Hx; rewrite -(fK x) (linearlfE lg).
1:  clear -P1 egt0; case: m / P1 f g lg=> f g lg.
2:  clear -P1 egt0; case: n / P1 f g lg=> f g lg.
1,2: by rewrite mx_dim0 linear0 subr0 normr0 ltW.
pose vf := (fun v : V =>castmx (Em, En) (f v) ).
pose vg := (fun r=>g (castmx (esym Em, esym En) r)).
have lvf : linear vf by move=>a x y; rewrite /vf (linearlfE lf) !linearP.
have lvg : linear vg by move=>a x y; rewrite /vg (linearlfE lg) !linearP.
have bvf : bijective vf by exists vg=>x;rewrite /vf/vg ?gK castmx_comp castmx_id ?fK.
have bvg : bijective vg by exists vf=>x;rewrite /vf/vg ?gK castmx_comp castmx_id ?fK.
(* have cf: continuous vf by exact: (bijective_to_cmx_continuous lvf bvf). *)
have cg: continuous vg by exact: (bijective_of_cmx_continuous lvg bvg).
suff fgK: (vg \o vf)%FUN = id. suff ccf: cauchy_ex (vf @ F).
- move: ccf=>/cauchy_exP/cauchy_cvg P1.
  suff: cvg ((vg \o vf)%FUN x @[x --> F])%classic by rewrite fgK.
  by move: P1=>/cvg_ex/=[a Pa]; apply/cvg_ex; exists (vg a); 
  apply: continuous_cvg=>[|//]; apply cg.
- move: (bounded_normr_cmxnorm lvf bvf)=>[[c1 [c1gt0 Pc1]] [c2 [c2gt0 Pc2]]].
  move=>e egt0; have ecgt0: e / c2 > 0 by apply divr_gt0.
  move: (F_cauchy _ ecgt0)=>[x Px].
  exists (vf x); rewrite /= /nbhs/= -filterP_strong.
  exists (ball x (e/c2)); exists Px; move=>y. rewrite /= -!ball_normE/= =>P2.
  rewrite (linearlfE lvf) -linearB/= /normr/=. apply (le_lt_trans (Pc2 _)).
  by rewrite mulrC -ltr_pdivl_mulr.
Unshelve. 2,3:  end_near.
- by apply/funext=>x; rewrite /vf/vg/= castmx_comp castmx_id fK.
Qed.

Lemma V_complete (V : finNormedModType C) (F : set (set V)) : 
  ProperFilter F -> cauchy F -> cvg F.
Proof. apply: (@V_complete_sub _ _ _ (@v2r _ V) _ v2r_bij); exact: linearP. Qed.

Local Canonical finNormedMod_completeType (V : finNormedModType C) := 
  CompleteType V (@V_complete V).
Local Canonical finNormedMod_CompleteNormedModule (V : finNormedModType C) := 
  Eval hnf in [completeNormedModType C of V].
Local Canonical vorderFinNormedMod_completeType (V : vorderFinNormedModType C) := 
  CompleteType V (@V_complete V).
Local Canonical vorderFinNormedMod_CompleteNormedModule (V : vorderFinNormedModType C) := 
  Eval hnf in [completeNormedModType C of V].

End FinNormedModTypeComplete.

Arguments bijective_to_cmx_cvgE [R V m n f u a].
Arguments bijective_of_cmx_cvgE [R V m n f u a].
Arguments bijective_to_cmx_is_cvgE [R V m n f u].
Arguments bijective_of_cmx_is_cvgE [R V m n f u].
Arguments bijective_to_cmx_limE [R V m n f u].
Arguments bijective_of_cmx_limE [R V m n f u].

Lemma addr_continuous {K : numFieldType} {V : pseudoMetricNormedZmodType K} a : 
  continuous (fun z : V => a + z).
Proof.
by move=> x; apply: (cvg_comp2 (cvg_cst _) cvg_id (@add_continuous _ _ (_, _))).
Qed.

Lemma addl_continuous {K : numFieldType} {V : pseudoMetricNormedZmodType K} a : 
  continuous (fun z : V => z + a).
Proof.
by move=> x; apply: (cvg_comp2 cvg_id (cvg_cst _) (@add_continuous _ _ (_, _))).
Qed.

Section FinNormedModTheory.
Variable (R : realType) (V : finNormedModType R[i]).
Import Num.Theory Vector.InternalTheory.
Implicit Type (f g: nat -> V) (n: nat) (s a b : V).

(* default norm is a vnorm  *)
Canonical finNormedMod_vnorm := Vnorm (@ler_norm_add _ V) (@normr0_eq0 _ V) (@normmZ _ V).

Local Canonical finNormedMod_CompleteNormedModule.

Lemma Vhausdorff : hausdorff_space V.
Proof. exact: norm_hausdorff. Qed.

Lemma vcvg_limE f a : f --> a <-> lim f = a /\ cvg f.
Proof. exact: (cvg_limE f a Vhausdorff). Qed.

Lemma vcvg_map f a (U : completeType) (h : V -> U) :
  continuous h -> f --> a -> (h \o f) --> h a.
Proof. 
move=>ch cvgf; apply: (@cvg_fmap _ _ [filter of f] a h).
by apply ch. by apply cvgf.
Qed.

Lemma vcvg_mapV (U : completeType) (h : U -> V) (h' : nat -> U) (a : U) :
  continuous h -> h' --> a -> (h \o h') --> h a.
Proof. 
move=>ch cvgf; apply: (@cvg_fmap _ _ [filter of h'] a h).
by apply ch. by apply cvgf.
Qed.

Lemma is_vcvg_map f (U : completeType) (h : V -> U) :
  continuous h -> cvg f -> cvg (h \o f).
Proof.
move=>P1 /cvg_ex=>[/= [a Pa]]. apply/cvg_ex.
exists (h a). by move: (vcvg_map P1 Pa).
Qed.

Lemma is_vcvg_mapV (U : completeType) (h : U -> V) (h' : nat -> U) :
  continuous h -> cvg h' -> cvg (h \o h').
Proof.
move=>P1 /cvg_ex=>[/= [a Pa]]. apply/cvg_ex.
exists (h a). by move: (vcvg_mapV P1 Pa).
Qed.

Lemma vlim_map f a (U : completeType) (h : V -> U) :
  hausdorff_space U -> continuous h -> cvg f -> lim (h \o f) = h (lim f).
Proof. by move=>hV ch; move/(vcvg_map ch)/cvg_lim=>/(_ hV). Qed.

Lemma vlim_mapV (U : completeType) (h : U -> V) (h' : nat -> U) :
  continuous h -> cvg h' -> lim (h \o h') = h (lim h').
Proof. by move=>ch; move/(vcvg_mapV ch)/cvg_lim=>/(_ Vhausdorff). Qed.

Lemma vcvg_limP f a :
  f --> a <-> forall e, 0 < e -> exists N, forall n,  (N <= n)%N -> `|f n - a| < e.
Proof. exact: cvg_limP. Qed.

Lemma vcvg_subseqP f a : 
  f --> a <-> (forall (h: nat -> nat), (forall n, (h n.+1 > h n)%N) -> (f \o h) --> a).
Proof. exact: cvg_subseqP. Qed.

Lemma vcvg_subseqPN f a :
  ~ (f --> a) <-> exists e (h: nat -> nat), 
    (forall n, (h n.+1 > h n)%N) /\ 0 < e /\ (forall n, `|(f \o h) n - a| >= e).
Proof. exact: cvg_subseqPN. Qed.

(* vnorm V transform to vnorm of matrix *)
Program Definition v2r_vnorm (f : vnorm V) := @VNorm.Vnorm _ _ (fun x=>f (r2v x)) _ _ _.
Next Obligation.
by move=>f x y /=; rewrite linearD/= lev_norm_add.
Qed.
Next Obligation.
by move=>f x /= /normv0_eq0; rewrite -{2}(r2vK x)=>->; rewrite linear0.
Qed.
Next Obligation.
by move=>f a x/=; rewrite !linearZ/= normvZ.
Qed.

Program Definition r2v_vnorm (f : vnorm _) := @VNorm.Vnorm _ V (fun x=>f (v2r x)) _ _ _.
Next Obligation.
by move=>f x y /=; rewrite linearD/= lev_norm_add.
Qed.
Next Obligation.
by move=>f x /= /normv0_eq0; rewrite -{2}(v2rK x)=>->; rewrite linear0.
Qed.
Next Obligation.
by move=>f a x/=; rewrite !linearZ/= normvZ.
Qed.

Lemma r2vK_vnorm (f : vnorm _) x : v2r_vnorm (r2v_vnorm f) x = f x.
Proof. by rewrite /= r2vK. Qed.
Lemma v2rK_vnorm (f : vnorm V) x : r2v_vnorm (v2r_vnorm f) x = f x.
Proof. by rewrite /= v2rK. Qed.
Lemma r2v_vnormE (f : vnorm _) x : f x = r2v_vnorm f (r2v x).
Proof. by rewrite /= r2vK. Qed.
Lemma v2r_vnormE (f : vnorm V) x : f x = v2r_vnorm f (v2r x).
Proof. by rewrite /= v2rK. Qed.

(* equivalence of vnorm of V *)
(* linear continuous *)
Lemma normv_bounded (f g : vnorm V):
  exists2 c : R[i], 0 < c & forall x, f x <= c * g x.
Proof.
move: (cmxnormv_bounded (v2r_vnorm f) (v2r_vnorm g))=>[c cgt0 Pc].
exists c=>// x; by rewrite !v2r_vnormE.
Qed.

Lemma v2r_continuous : continuous (@v2r _ V).
Proof. apply: (bijective_to_cmx_continuous _ v2r_bij); exact: linearP. Qed.

Lemma r2v_continuous : continuous (@r2v _ V).
Proof. apply: (bijective_of_cmx_continuous _ r2v_bij); exact: linearP. Qed.

Lemma normv_ubounded (f : vnorm V) : 
  exists2 c, 0 < c & forall x, f x <= c * `| x |.
Proof. exact: normv_bounded. Qed.

Lemma normv_lbounded (f : vnorm V) : 
  exists2 c, 0 < c & forall x, c * `| x | <= f x.
Proof.
move: (normv_bounded finNormedMod_vnorm f)=>[c cgt0 Pc].
by exists (c^-1)=>[|x]; rewrite ?ler_pdivr_mull// ?Pc// invr_gt0.
Qed.

Lemma cauchy_seqv_defaultE f :
  cauchy_seqv finNormedMod_vnorm f <-> cauchy_seq f.
Proof. by []. Qed.

Lemma cauchy_seqv_eq (nv1 nv2 : vnorm V) f :
  cauchy_seqv nv1 f <-> cauchy_seqv nv2 f.
split.
move: (normv_bounded nv2 nv1). 2: move: (normv_bounded nv1 nv2).
all: move=> [c Pc le_mn] P e Pe.
all: have Pec: 0 < (e / c) by apply divr_gt0.
all: move: (P (e/c) Pec )=>[N PN]; exists N=>s t Ps Pt.
all: apply: (le_lt_trans (le_mn (f s - f t))).
all: by rewrite -ltr_pdivl_mull// mulrC PN.
Qed.

Lemma cauchy_seqv_cvg (nv : vnorm V) f :
  cauchy_seqv nv f <-> cvg f.
Proof.
rewrite (@cauchy_seqv_eq _ finNormedMod_vnorm).
exact: cauchy_seqP.
Qed.

Lemma normv_continuous (nv : vnorm V) : continuous nv.
Proof.
suff <-: (v2r_vnorm nv) \o v2r = nv.
apply: continuous_comp_simp. apply: v2r_continuous.
apply cmxnormv_continuous.
by apply/funext=>x /=; rewrite v2rK.
Qed.

Local Notation MV := 'rV[R[i]]_(Vector.dim V).

Lemma v2r_cvgE (u : nat -> V) (a : V): u --> a = ((v2r \o u)%FUN --> v2r a).
Proof. apply: (bijective_to_cmx_cvgE _ v2r_bij); exact: linearP. Qed.

Lemma r2v_cvgE (u : nat -> MV) (a : MV) : u --> a = ((r2v \o u)%FUN --> r2v a).
Proof. apply: (bijective_of_cmx_cvgE _ r2v_bij); exact: linearP. Qed.

Lemma v2r_is_cvgE (u : nat -> V) : cvg u = cvg (v2r \o u)%FUN.
Proof. apply: (bijective_to_cmx_is_cvgE _ v2r_bij); exact: linearP. Qed.

Lemma r2v_is_cvgE (u : nat -> MV) : cvg u = cvg (r2v \o u)%FUN.
Proof. apply: (bijective_of_cmx_is_cvgE _ r2v_bij). exact: linearP. Qed.

Lemma v2r_limE (u : nat -> V) : cvg u -> lim (v2r \o u)%FUN = v2r (lim u).
Proof. apply: (bijective_to_cmx_limE _ v2r_bij); exact: linearP. Qed.

Lemma r2v_limE (u : nat -> MV) : cvg u -> lim (r2v \o u)%FUN = r2v (lim u).
Proof. apply: (bijective_of_cmx_limE _ r2v_bij); exact: linearP. Qed.

End FinNormedModTheory.

Lemma scalarlfE (R : ringType) (U : lmodType R) (f : U -> R) (lf: scalar f) :
  f = Linear lf. Proof. by []. Qed.

Section LinearContinuous.
Variable (R : realType).
Import Vector.InternalTheory.

Lemma linear_continuous (U V: finNormedModType R[i]) (f : {linear U -> V}) :
  continuous f.
Proof.
pose g x := v2r (f (r2v x)); suff <-: r2v \o g \o v2r = f.
apply: continuous_comp_simp; first by apply: v2r_continuous.
apply: continuous_comp_simp; last by apply: r2v_continuous.
by apply/cmxlinear_continuous=>a x y; rewrite /g !linearP.
by apply/funext=>x; rewrite /g/= !v2rK.
Qed.

Lemma linear_continuousP (U V: finNormedModType R[i]) (f : U -> V) :
  linear f -> continuous f.
Proof. move=>lf; rewrite (linearlfE lf); exact: linear_continuous. Qed.

Lemma linear_cvg (U V: finNormedModType R[i]) (f : {linear U -> V}) (u : nat -> U) (a : U) :
  u --> a -> f \o u --> f a.
Proof. move=>cu. apply: continuous_cvg=>//. apply: linear_continuous. Qed.

Lemma linear_cvgP (U V: finNormedModType R[i]) (f : U -> V) (u : nat -> U) (a : U) :
  linear f -> u --> a -> f \o u --> f a.
Proof. move=>lf; rewrite (linearlfE lf); exact: linear_cvg. Qed.

Lemma linear_is_cvg (U V: finNormedModType R[i]) (f : {linear U -> V}) (u : nat -> U) :
  cvg u -> cvg (f \o u).
Proof. move/cvg_ex=>[a Pa]; apply/cvg_ex; exists (f a); by apply: linear_cvg. Qed.

Lemma linear_is_cvgP (U V: finNormedModType R[i]) (f : U -> V) (u : nat -> U) :
  linear f -> cvg u -> cvg (f \o u).
Proof. move=>lf; rewrite (linearlfE lf); exact: linear_is_cvg. Qed.

Lemma linear_lim (U V: finNormedModType R[i]) (f : {linear U -> V}) (u : nat -> U) :
  cvg u -> lim (f \o u) = f (lim u).
Proof. by move=>cu; apply: cvg_lim; [apply: Vhausdorff | apply: linear_cvg]. Qed.

Lemma linear_limP (U V: finNormedModType R[i]) (f : U -> V) (u : nat -> U) :
  linear f -> cvg u -> lim (f \o u) = f (lim u).
Proof. move=>lf; rewrite (linearlfE lf); exact: linear_lim. Qed.

Lemma scalar_continuous (U: finNormedModType R[i]) (f : {scalar U}) :
  continuous f.
Proof.
pose g x := (f (r2v x)); suff <-: g \o v2r = f.
apply: continuous_comp_simp; first by apply: v2r_continuous.
by apply/cmxscalar_continuous=>a x y; rewrite /g linearP/= !scalarP.
by apply/funext=>x; rewrite /g/= !v2rK.
Qed.

Lemma scalar_continuousP (U: finNormedModType R[i]) (f : U -> R[i]) :
  scalar f -> continuous f.
Proof. move=>lf; rewrite (scalarlfE lf); exact: scalar_continuous. Qed.

Lemma scalar_cvg (U: finNormedModType R[i]) (f : {scalar U}) (u : nat -> U) (a : U) :
  u --> a -> f \o u --> f a.
Proof. move=>cu. apply: continuous_cvg=>//. apply: scalar_continuous. Qed.

Lemma scalar_cvgP (U: finNormedModType R[i]) (f : U -> R[i]) (u : nat -> U) (a : U) :
  scalar f -> u --> a -> f \o u --> f a.
Proof. move=>lf; rewrite (scalarlfE lf); exact: scalar_cvg. Qed.

Lemma scalar_is_cvg (U: finNormedModType R[i]) (f : {scalar U}) (u : nat -> U) :
  cvg u -> cvg (f \o u).
Proof. move/cvg_ex=>[a Pa]; apply/cvg_ex; exists (f a); by apply: scalar_cvg. Qed.

Lemma scalar_is_cvgP (U: finNormedModType R[i]) (f : U -> R[i]) (u : nat -> U) :
  scalar f -> cvg u -> cvg (f \o u).
Proof. move=>lf; rewrite (scalarlfE lf); exact: scalar_is_cvg. Qed.

Lemma scalar_lim (U: finNormedModType R[i]) (f : {scalar U}) (u : nat -> U) :
  cvg u -> lim (f \o u) = f (lim u).
Proof. by move=>cu; apply: cvg_lim; [apply: Vhausdorff | apply: scalar_cvg]. Qed.

Lemma scalar_limP (U: finNormedModType R[i]) (f : U -> R[i]) (u : nat -> U) :
  scalar f -> cvg u -> lim (f \o u) = f (lim u).
Proof. move=>lf; rewrite (scalarlfE lf); exact: scalar_lim. Qed.

Lemma linearl_continuous (U V W: finNormedModType R[i]) (f : {bilinear U -> V -> W}) (x : V):
  continuous (f^~ x).
Proof. have <-: applyr f x = f^~x by apply/funext/applyrE. apply: linear_continuous. Qed. 

Lemma linearl_cvg (U V W: finNormedModType R[i]) (f : {bilinear U -> V -> W}) (x : V)
  (u : nat -> U) (a : U):
  u --> a -> (f^~x) \o u --> f a x.
Proof. have <-: applyr f x = f^~x by apply/funext/applyrE. apply: linear_cvg. Qed.

Lemma linearl_is_cvg (U V W: finNormedModType R[i]) (f : {bilinear U -> V -> W}) (x : V) 
  (u : nat -> U) :
  cvg u -> cvg (f^~x \o u).
Proof. have <-: applyr f x = f^~x by apply/funext/applyrE. apply: linear_is_cvg. Qed.

Lemma linearl_lim (U V W: finNormedModType R[i]) (f : {bilinear U -> V -> W}) (x : V) 
  (u : nat -> U) :
  cvg u -> lim (f^~x \o u) = f (lim u) x.
Proof. have <-: applyr f x = f^~x by apply/funext/applyrE. apply: linear_lim. Qed.

Lemma linearr_continuous (U V W: finNormedModType R[i]) (f : {bilinear U -> V -> W}) (x : U):
  continuous (f x).
Proof. exact: linear_continuous. Qed. 

Lemma linearr_cvg (U V W: finNormedModType R[i]) (f : {bilinear U -> V -> W}) (x : U)
  (u : nat -> V) (a : V):
  u --> a -> (f x) \o u --> f x a.
Proof. exact: linear_cvg. Qed.

Lemma linearr_is_cvg (U V W: finNormedModType R[i]) (f : {bilinear U -> V -> W}) (x : U) 
  (u : nat -> V) :
  cvg u -> cvg (f x \o u).
Proof. exact: linear_is_cvg. Qed.

Lemma linearr_lim (U V W: finNormedModType R[i]) (f : {bilinear U -> V -> W}) (x : U) 
  (u : nat -> V) :
  cvg u -> lim (f x \o u) = f x (lim u).
Proof. exact: linear_lim. Qed.

Lemma linear_to_cmx_continuous (U : finNormedModType R[i]) m n 
  (f : {linear U -> 'M[R[i]]_(m,n)}) :
  continuous f.
Proof.
pose g x := (f (r2v x)); suff <-: g \o v2r = f.
apply: continuous_comp_simp; first by apply: v2r_continuous.
by apply/cmxlinear_continuous=>a x y; rewrite /g !linearP.
by apply/funext=>x; rewrite /g/= !v2rK.
Qed.

Lemma linear_to_cmx_continuousP (U : finNormedModType R[i]) m n (f : U -> 'M[R[i]]_(m,n)) :
  linear f -> continuous f.
Proof. move=>lf; rewrite (linearlfE lf); exact: linear_to_cmx_continuous. Qed.

Lemma linear_of_cmx_continuous (U : finNormedModType R[i]) m n 
  (f : {linear 'M[R[i]]_(m,n) -> U}) :
  continuous f.
Proof.
pose g x := v2r (f x); suff <-: r2v \o g = f.
apply: continuous_comp_simp; last by apply: r2v_continuous.
by apply/cmxlinear_continuous=>a x y; rewrite /g !linearP.
by apply/funext=>x; rewrite /g/= !v2rK.
Qed.

Lemma linear_of_cmx_continuousP (U : finNormedModType R[i]) m n (f : 'M[R[i]]_(m,n) -> U) :
  linear f -> continuous f.
Proof. move=>lf; rewrite (linearlfE lf); exact: linear_of_cmx_continuous. Qed.

Lemma closed_linearP (U V : finNormedModType R[i]) (f : U -> V)
  (A : set V) :
  linear f -> closed A -> closed (f @^-1` A).
Proof. by move=>lf; apply closed_comp=>x _; apply linear_continuousP. Qed.

Lemma open_linearP (U V : finNormedModType R[i]) (f : U -> V)
  (A : set V) :
  linear f -> open A -> open (f @^-1` A).
Proof. by move=>lf; apply open_comp=>x _; apply linear_continuousP. Qed.

Lemma closed_linear (U V : finNormedModType R[i]) (f : {linear U -> V})
  (A : set V) : closed A -> closed (f @^-1` A).
Proof. apply closed_linearP; exact: linearP. Qed. 

Lemma open_linear (U V : finNormedModType R[i]) (f : {linear U -> V})
  (A : set V) : open A -> open (f @^-1` A).
Proof. apply open_linearP; exact: linearP. Qed. 

Lemma closed_to_cmx_linearP (U : finNormedModType R[i]) m n 
  (f : U -> 'M[R[i]]_(m,n)) (A : set 'M[R[i]]_(m,n)):
  linear f -> closed A -> closed (f @^-1` A).
Proof. by move=>lf; apply closed_comp=>x _; apply linear_to_cmx_continuousP. Qed.

Lemma closed_to_cmx_linear (U : finNormedModType R[i]) m n 
  (f : {linear U -> 'M[R[i]]_(m,n)}) (A : set 'M[R[i]]_(m,n)):
  closed A -> closed (f @^-1` A).
Proof. apply closed_to_cmx_linearP; exact: linearP. Qed.

Lemma open_to_cmx_linearP (U : finNormedModType R[i]) m n 
  (f : U -> 'M[R[i]]_(m,n)) (A : set 'M[R[i]]_(m,n)):
  linear f -> open A -> open (f @^-1` A).
Proof. by move=>lf; apply open_comp=>x _; apply linear_to_cmx_continuousP. Qed.

Lemma open_to_cmx_linear (U : finNormedModType R[i]) m n 
  (f : {linear U -> 'M[R[i]]_(m,n)}) (A : set 'M[R[i]]_(m,n)):
  open A -> open (f @^-1` A).
Proof. apply open_to_cmx_linearP; exact: linearP. Qed.

Lemma closed_of_cmx_linearP (U : finNormedModType R[i]) m n 
  (f : 'M[R[i]]_(m,n) -> U) (A : set U):
  linear f -> closed A -> closed (f @^-1` A).
Proof. by move=>lf; apply closed_comp=>x _; apply linear_of_cmx_continuousP. Qed.

Lemma closed_of_cmx_linear (U : finNormedModType R[i]) m n 
  (f : {linear 'M[R[i]]_(m,n) -> U}) (A : set U):
  closed A -> closed (f @^-1` A).
Proof. apply closed_of_cmx_linearP; exact: linearP. Qed.

Lemma open_of_cmx_linearP (U : finNormedModType R[i]) m n 
  (f : 'M[R[i]]_(m,n) -> U) (A : set U):
  linear f -> open A -> open (f @^-1` A).
Proof. by move=>lf; apply open_comp=>x _; apply linear_of_cmx_continuousP. Qed.

Lemma open_of_cmx_linear (U : finNormedModType R[i]) m n 
  (f : {linear 'M[R[i]]_(m,n) -> U}) (A : set U):
  open A -> open (f @^-1` A).
Proof. apply open_of_cmx_linearP; exact: linearP. Qed.

End LinearContinuous.

Section VOrderFinNormedModTheory.
Variable (R : realType) (V : vorderFinNormedModType R[i]).
Local Notation M := 'rV[R[i]]_(Vector.dim V).
Import Vector.InternalTheory.

Lemma closed_gev0: closed [set x : V | (0 : V) ⊑ x].
Proof. by case: V=>?[???[?]]. Qed.

Definition v2r_vorderle (x y : M) := r2v x ⊑ r2v y.
Definition v2r_vorderlt (x y : M) := r2v x ⊏ r2v y.

Lemma v2r_vorderlt_def (x y : M): v2r_vorderlt x y = (y != x) && (v2r_vorderle x y).
Proof. by rewrite /v2r_vorderlt lt_def (can_eq r2vK). Qed.

Lemma v2r_vorderle_anti : antisymmetric v2r_vorderle.
Proof. by move=>x y; rewrite /v2r_vorderle=>/le_anti/r2v_inj. Qed.

Lemma v2r_vorderle_refl : reflexive v2r_vorderle.
Proof. by move=>x; exact: le_refl. Qed.

Lemma v2r_vorderle_trans : transitive v2r_vorderle.
Proof. by move=>x y z; exact: le_trans. Qed. 

Definition v2r_vorderle_porderMixin := LePOrderMixin 
  v2r_vorderlt_def v2r_vorderle_refl v2r_vorderle_anti v2r_vorderle_trans.
Definition v2r_vorderle_porderType := 
  POrderType vorder_display M v2r_vorderle_porderMixin.
Local Canonical v2r_vorderle_porderType.

Lemma v2r_lemx_add2r : forall (z x y : M), x ⊑ y -> x + z ⊑ y + z.
Proof. by move=>z x y; rewrite /Order.le/= /v2r_vorderle !linearD/= lev_add2r. Qed.

Lemma v2r_lemx_pscale2lP : forall (e : R[i]) (x y : M), 0 < e -> x ⊑ y -> e *: x ⊑ e *: y.
Proof. 
by move=>e x y egt0; rewrite /Order.le/= 
  /v2r_vorderle !linearZ/=; apply lev_pscale2lP.
Qed.

Lemma v2r_closed_gemx0: closed [set x : M | (0 : M) ⊑ x].
Proof.
rewrite (_ : mkset _ = r2v @^-1` [set x : V | (0 : V) ⊑ x]).
apply: closed_comp=>[? _|]; [apply: r2v_continuous | apply: closed_gev0].
by rewrite predeqE {1}/Order.le/= /v2r_vorderle linear0.
Qed.

Definition v2r_mxnormcvg := Cmxnormcvg (v2r_vnorm (finNormedMod_vnorm V))
  v2r_lemx_add2r v2r_lemx_pscale2lP v2r_closed_gemx0.

Lemma nondecreasing_oppv (u_ : V ^nat) :
  nondecreasing_seq (- u_) = nonincreasing_seq u_.
Proof. by rewrite propeqE; split => du x y /du; rewrite lev_opp2. Qed.

Lemma nonincreasing_oppv (u_ : V ^nat) :
  nonincreasing_seq (- u_) = nondecreasing_seq u_.
Proof. by rewrite propeqE; split => du x y /du; rewrite lev_opp2. Qed.

Lemma decreasing_oppv (u_ : V ^nat) :
  decreasing_seq (- u_) = increasing_seq u_.
Proof. by rewrite propeqE; split => du x y; rewrite -du lev_opp2. Qed.

Lemma increasing_oppv (u_ : V ^nat) :
  increasing_seq (- u_) = decreasing_seq u_.
Proof. by rewrite propeqE; split => du x y; rewrite -du lev_opp2. Qed.

Lemma lbounded_by_opp (b : V) (u : V ^nat) :
  lbounded_by (-b) (- u) = ubounded_by b u.
Proof. 
by rewrite propeqE; split => bu i; move: (bu i); 
  rewrite {2}/GRing.opp/= lev_opp2.
Qed.

Lemma ubounded_by_opp (b : V) (u : V ^nat) :
  ubounded_by (-b) (- u) = lbounded_by b u.
Proof. 
by rewrite propeqE; split => bu i; move: (bu i); 
  rewrite {2}/GRing.opp/= lev_opp2.
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
by apply/funext=>x; rewrite /= -{2}oppr0 lev_opp2. 
Qed.

Lemma open_nlev y :  open [set x : V | ~ x ⊑ y].
Proof.
rewrite (_ : mkset _ = [set t | [set x : V | ~ - y ⊑ x] (- t)]).
by move: (@opp_continuous _ V)=>/continuousP/=/(_ _ (open_ngev (-y))).
by apply/funext=>x; rewrite /= lev_opp2.
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

Lemma lim_gev_near (x : V) (u : V ^nat) : 
  cvg u -> (\forall n \near \oo, x ⊑ u n) -> x ⊑ lim u.
Proof.
move=> /[swap] /(closed_cvg (fun y=>x ⊑ y))/= P1; apply/P1/closed_gev.
Qed.

Lemma lim_lev_near (x : V) (u : V ^nat) : 
  cvg u -> (\forall n \near \oo, u n ⊑ x) -> lim u ⊑ x.
Proof.
move=> /[swap] /(closed_cvg (fun y : V=>y ⊑ x))/= P1;apply/P1/closed_lev.
Qed.

Lemma lev_lim_near (u_ v_ : V ^nat) : cvg u_ -> cvg v_ ->
  (\forall n \near \oo, u_ n ⊑ v_ n) -> lim u_ ⊑ lim v_.
Proof.
move=> uv cu cv; rewrite -(subv_ge0) -limB//.
apply: lim_gev_near=>//. apply: is_cvgB=>//.
by apply: filterS cv => k; rewrite (subv_ge0).
Qed.

Lemma lim_gev (x : V) (u : V ^nat) : cvg u -> lbounded_by x u -> x ⊑ lim u.
Proof.
by move=>P1 P2; apply: (lim_gev_near P1); apply: nearW.
Qed.

Lemma lim_lev (x : V) (u : V ^nat) : cvg u -> ubounded_by x u -> lim u ⊑ x.
Proof.
by move=>P1 P2; apply: (lim_lev_near P1); apply: nearW.
Qed.

Lemma lev_lim (u v : V^nat) : cvg u -> cvg v ->
  (forall n, u n ⊑ v n) -> lim u ⊑ lim v.
Proof.
by move=>P1 P2 P3; apply: (lev_lim_near P1 P2); apply: nearW.
Qed.

Lemma nondecreasing_cvg_lev (u : V ^nat) :
       nondecreasing_seq u -> cvg u -> ubounded_by (lim u) u.
Proof.
move=>Ph Pc i; apply: lim_gev_near=>//; exists i=>// j; apply Ph.
Qed.

Lemma nonincreasing_cvg_gev (u : V ^nat) : 
  nonincreasing_seq u -> cvg u -> lbounded_by (lim u) u.
Proof.
move=>Ph Pc i; apply: lim_lev_near=>//; exists i=>// j; apply Ph.
Qed.

Lemma vnondecreasing_is_cvg (f : nat -> V) (b : V) :
  nondecreasing_seq f -> ubounded_by b f -> cvg f.
Proof.
move=>P1 P2. pose g := (v2r \o f).
have P3: nondecreasing_seq g by move=>n m /P1; rewrite {2}/Order.le/= /v2r_vorderle !v2rK.
have P4: ubounded_by (v2r b) g by move=>i; rewrite /Order.le/= /v2r_vorderle !v2rK.
move: (cmxnondecreasing_is_cvg v2r_mxnormcvg P3 P4).
have <-: r2v \o g = f by apply/funext=>x/=; rewrite v2rK.
move=> /cvg_ex[l fxl]; apply/cvg_ex; exists (r2v l).
by apply: continuous_cvg => //; apply: r2v_continuous.
Qed.

Lemma vnonincreasing_is_cvg (f : nat -> V) (b : V) :
    nonincreasing_seq f -> lbounded_by b f -> cvg f.
Proof.
rewrite -(nondecreasing_oppv) -(ubounded_by_opp) -is_cvgNE.
exact: vnondecreasing_is_cvg.
Qed.

End VOrderFinNormedModTheory.


