From HB Require Import structures.
From mathcomp Require Import all_ssreflect finmap.
From quantum Require Import compat.
From quantum.external Require Import complex.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import topology normedtype sequences.
From mathcomp Require Import interval_inference.
From mathcomp Require Import -(notations) sesquilinear.
Require Import mcextra mcaextra notation mxpred extnum ctopology svd mxnorm.
Require Import hermitian inhabited prodvect.
From quantum Require Import tensor.
Require Import quantum hspace inhabited summable qreg qmem.
From quantum.dirac Require Import hstensor.
From Stdlib Require Import Program.Equality String.
(* Require Import -(notations) Program. *)

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Local Notation C := hermitian.C.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Section summable_linear.
Import Summable.Exports ExtNumTopology HermitianTopology.
Local Open Scope ring_scope.
Context {I : choiceType} {R : realType} {V W : normedVectType R[i]}.

Lemma linear_bounded (f : {linear V -> W}) : 
  exists k, 0 < k /\ forall v, `|f v| <= k * `|v|.
Proof.
move: (pselect (exists v, `|f v| != 0)%classic)=>[[v Pv]|Ps] ; last first.
  exists 1; split=>[|v]; first by apply: ltr01.
  by move: Ps; rewrite mul1r -forallNP=>/(_ v)/negP; rewrite negbK=>/eqP->.
have Pc: compact [set x : V | `|x| = 1].
  apply: (subclosed_compact _ (compact_norm_le (V := V) (e := 1)))=>[|?/=->//].
  rewrite (_ : mkset _ = (fun x=>`|x|) @^-1` [set x : R[i] | x = 1])%classic.
  by apply/funext=>i /=.
  apply: closed_comp=>[? _ |]; [apply: norm_continuous | apply: cclosed_eq].
pose S := ((fun x=>`|x|) @` (f @` [set x | `|x| = 1]))%classic.
have Sr: (S `<=` [set` Num.real])%classic.
  by move=>i; rewrite /S/==>[[y Py <-]]; apply/normr_real.
have Pc1: compact S.
  apply: continuous_compact. apply/continuous_subspaceT/norm_continuous.
  apply: continuous_compact=>//. apply/continuous_subspaceT/linear_continuous.
have v0: v != 0 by apply/negP=>/eqP v0; move: Pv; rewrite v0 linear0 normr0 eqxx.
have Sv : forall v, v != 0 -> S `|f (`|v|^-1 *: v)|.
  move=>u Pu; rewrite/S/=; exists (f (`|u|^-1 *: u))=>//; exists (`|u|^-1 *: u)=>//.
  by rewrite normrZ ger0_norm ?invr_ge0// mulVf// normr_eq0.
have s0 : (S !=set0)%classic by exists `|f (`|v|^-1 *: v)|; apply: Sv.
move: (extNum_compact_max Sr Pc1 s0)=>[e Pe1 Pe2].
have egt0: 0 < e. 
  apply/(lt_le_trans _ (Pe2 _ (Sv _ v0))); rewrite linearZ/= normrZ.
  by rewrite ger0_norm ?invr_ge0// mulr_gt0// ?invr_gt0 normr_gt0// -normr_eq0.
exists e; split=>// u.
case: (@eqP _ u 0)=>[->|]; first by rewrite linear0 !normr0 mulr0.
move=>/eqP Pu; move: (Pe2 _ (Sv _ Pu)).
by rewrite linearZ/= normrZ ger0_norm ?invr_ge0// ler_pdivrMl 1?mulrC// normrE.
Qed.

Lemma cvg_linear_sum (x : I -> V) (f : {linear V -> W}) :
  cvg ((psum x) @ totally)%classic -> f (sum x) = sum (f \o x)%FUN.
Proof. apply/cvg_linear_sumG/linear_bounded. Qed.

Lemma cvg_linearP_sum (x : I -> V) (f : V -> W) : linear f ->
  cvg ((psum x) @ totally)%classic -> f (sum x) = sum (f \o x)%FUN.
Proof. by move=>Pf; rewrite (linearlfE Pf); apply: cvg_linear_sum. Qed.

Lemma summable_linear_sum (x : {summable I -> V}) (f : {linear V -> W}) :
  f (sum x) = sum (f \o x)%FUN.
Proof. apply/summable_linear_sumG/linear_bounded. Qed.

End summable_linear.

Module Summable_Reindex.
Import Summable.Exports ExtNumTopology HermitianTopology.
Local Open Scope ring_scope.

Section Theory.
Lemma summableW (I : choiceType) (K : numFieldType) (V : normedZmodType K) (f : I -> V) :
  summable f <-> exists (M : K), forall J, psum (fun i=>`|f i|) J <= M.
Proof.
split=>[[M [S/= _ PS]]|[M PM]].
exists M=>J; apply/(le_trans (y := psum (fun i : I => `|f i|) (J `|` S)%fset)).
apply: psum_ler=>//; apply: fsubsetUl. apply: PS=>/=; apply/fsubsetUr.
exists M; near=>J; apply: PM.
Unshelve. end_near.
Qed.

Section Simple.
Context {I J : choiceType}.
Variable (h : J -> I) (h' : I -> option J).
Hypothesis (hK : pcancel h h') (h'K : ocancel h' h).
Variable (j0 : J).

Definition Si (S : {fset I}) := [fset i in S | h' i != None]%fset.
Definition h'' := (fun i => match h' i with | Some j => j | None => j0 end).
Definition Sj (S : {fset I}) := (h'' @` (Si S))%fset.

Lemma Sj_in_Si (S : {fset I}) : forall j : Sj S, h (val j) \in Si S.
Proof.
move=>[j/=]; move=>/imfsetP[i /imfsetP[i' /=]]; rewrite !inE=>/andP[] Pi1 Pi2 ->.
move: (h'K i')=>/[swap]; rewrite /oapp/h''; case E: (h' i').
by move=><-->; apply/andP=>[]. by rewrite E in Pi2.
Qed.
Definition hj (S : {fset I}) := (fun j : Sj S => [`(Sj_in_Si j)]%fset).

Lemma Si_in_Sj (S : {fset I}) : forall i : Si S, h'' (val i) \in Sj S.
Proof.
move=>[i /=/imfsetP[i']]; rewrite !inE=>/andP[]Pi1 Pi2 ->.
by apply/imfsetP; exists i'=>//; rewrite !inE/= Pi1 Pi2.
Qed.
Definition hi (S : {fset I}) := (fun i : Si S => [`(Si_in_Sj i)]%fset).

Lemma hiK (S : {fset I}) : cancel (@hi S) (@hj S).
Proof.
move=>[i/= Pi]; apply/val_inj. rewrite/=/h''.
move: Pi=>/imfsetP[i' /=]; rewrite inE=>/andP[] _ + ->.
by case E: (h' i')=>// _; move: (h'K i'); rewrite E.
Qed.
Lemma hjK (S : {fset I}) : cancel (@hj S) (@hi S).
Proof. by move=>[j/= Pj]; apply/val_inj; rewrite/=/h''; move: (hK j)=>->. Qed.

Lemma hj_bijective (S : {fset I}) : bijective (@hj S).
Proof. exists (@hi S). apply: hjK. apply: hiK. Qed.
Lemma hi_bijective (S : {fset I}) : bijective (@hi S).
Proof. exists (@hj S). apply: hiK. apply: hjK. Qed.

Lemma Si_le_S (S : {fset I}) : (Si S `<=` S)%fset.
Proof. by apply/fsubsetP=>i/imfsetP[i'/= + ->]; rewrite inE=>/andP[]. Qed.

Lemma Si_idp (S : {fset J}) : Si (h @` S)%fset = (h @` S)%fset.
Proof.
apply/eqP/fset_eqP=>i; apply/eqb_iff; split.
by move: (Si_le_S (h @` S)%fset)=>/fsubsetP/(_ i).
move=>/imfsetP[i' /= Pi ->]; apply/imfsetP; exists (h i')=>//=.
rewrite inE hK; apply/andP; split=>//.
by apply/imfsetP; exists i'.
Qed.

Context {R : realType} {C : extNumType R}.
Implicit Type (V : completeNormedModType C).

Definition Hf V (f : I -> V) := forall i, h' i = None -> f i = 0.

Lemma nin_Si_eq0 V (f : I -> V) (S : {fset I}) i : 
  Hf f -> i \in S -> i \notin Si S -> f i = 0.
Proof. rewrite inE/= inE negb_and=>+->/=; rewrite negbK=>P/eqP; apply: P. Qed.

Lemma psum_Si V (f : I -> V) (S : {fset I}) : Hf f -> psum f S = psum f (Si S).
Proof.
symmetry; rewrite/psum !(big_in_fsetE f); apply: big_fset_incl=>//. apply: Si_le_S.
by move=>i Pi /(nin_Si_eq0 H Pi)->.
Qed.

Lemma psum_Sj V (f : I -> V) (S : {fset I}) : 
  Hf f -> psum f S = psum (fun j => f (h j)) (Sj S).
Proof.
move=>P; rewrite psum_Si// /psum (reindex (@hj S))//=.
exists (@hi S)=>[+ _|+ _]; [apply: hjK | apply: hiK].
Qed.

Lemma reindex_summableP_simple V (f : I -> V) : 
  Hf f -> summable (f \o h)%FUN <-> summable f.
Proof.
split=>/summableW[M/= PM]; exists M; near=>S.
  rewrite psum_Sj=>[i/H|]; last by apply/PM.
  by rewrite /normf=>->; rewrite normr0.
suff ->: S = Sj (h @` S)%fset.
by rewrite/= -(psum_Sj (f := fun i => `|f i|))//; move=>i/H->; rewrite normr0.
apply/eqP/fset_eqP=>j; apply/eqb_iff; split.
move=>Pj; apply/imfsetP; exists (h j);
by rewrite/h'' ?inE/= hK//; apply/andP; split=>//; apply/imfsetP; exists j.
move=>/imfsetP[i/=/imfsetP[i' /=]]; rewrite !inE=>/andP[]/imfsetP[j'/=].
by move=>+->+->->; rewrite /h'' hK.
Unshelve. all: end_near.
Qed.

Lemma sum_reindex_simple V (f : I -> V) : 
  Hf f -> summable (f \o h)%FUN -> sum f = sum (f \o h)%FUN.
Proof.
move=>Pf Sf.
have /cvgrPdist_lt Pc: (psum (f \o h)%FUN @ totally --> sum (f \o h))%classic.
by move: (summable_cvg (f := Summable.build Sf)).
suff: (psum f @ totally --> sum (f \o h))%classic by move=>/cvg_lim<-.
apply/cvgrPdist_lt=>e egt0.
move: (Pc e egt0)=>[S _ PS].
exists (h @` S)%fset=>// T/= /fsubsetP PT.
rewrite psum_Sj//; apply: PS=>/=.
apply/fsubsetP=>j Pj; apply/imfsetP.
exists (h j); last by rewrite/h''//= hK.
rewrite !inE/= hK; apply/andP; split=>//.
by apply/(PT (h j))/imfsetP; exists j.
Qed.
End Simple.

Context {I J : choiceType} {R : realType} {C : extNumType R} (V : completeNormedModType C).
Variable (h : J -> I) (h' : I -> option J).
Hypothesis (hK : pcancel h h') (h'K : ocancel h' h).

Lemma reindex_summableP (f : I -> V) : 
  (forall i, h' i = None -> f i = 0) -> summable (f \o h)%FUN <-> summable f.
Proof.
move: (pselect (exists j0 : J, True))=>[[j0 _]|P].
by apply: reindex_summableP_simple.
move=>Pf; have IH: forall i, f i = 0.
  by move=>i; apply/Pf; case: (h' i)=>// a; exfalso; apply: P; exists a.
by split=> _; exists 0; near=>S; rewrite/psum big1//==>? _; rewrite /normf/= IH normr0.
Unshelve. all: end_near.
Qed.

Lemma sum_reindex (f : I -> V) : 
  (forall i, h' i = None -> f i = 0) ->
    summable (f \o h)%FUN -> sum f = sum (f \o h)%FUN.
Proof.
move: (pselect (exists j0 : J, True))=>[[j0 _]|P].
by apply: sum_reindex_simple.
move=>Pf _.
have IH: forall i, f i = 0.
  by move=>i; apply/Pf; case: (h' i)=>// a; exfalso; apply: P; exists a.
rewrite /sum.
have ->: psum f = fun => 0 by apply/funext=>S; rewrite/psum big1//.
have ->: psum (f \o h) = fun => 0 by apply/funext=>S; rewrite/psum big1//=.
by rewrite !lim_cst.
Qed.

Lemma sum_reindexV (f : I -> V) : 
  (forall i, h' i = None -> f i = 0) ->
    summable f -> sum (f \o h)%FUN = sum f.
Proof. by move=>P1 P2; rewrite sum_reindex// reindex_summableP. Qed.
End Theory.

Module Exports.

Definition reindex_summableP := @reindex_summableP.
Definition sum_reindex := @sum_reindex.
Definition sum_reindexV := @sum_reindexV.

Lemma norm_split {R : numFieldType} {V : normedZmodType R} (e : R) (z x y : V) :
  `|x - z| < e / 2 -> `|y - z| < e / 2 -> `|x - y| < e.
Proof.
move=>P1; rewrite -normrN opprB=>/(ltrD P1).
rewrite -splitr; apply/le_lt_trans/ler_distD.
Qed.

Section sum_sigma_cvg.
Context {I : choiceType} {R : realType} {C : extNumType R} {V : completeNormedModType C}.

Lemma summable_sigma_nat_cvg (h : I -> nat) (F : I -> V) : summable F -> 
    (sum (fun i : {i : I | (h i < n)%N} => F (val i)) @[n --> \oo] --> sum F)%classic.
Proof.
move=>SF. move: {+}SF=>/summableW[M PM].
have Pcn: forall n, cvg (psum (fun i : {i : I | (h i < n)%N} => F (val i)) @ totally)%classic.
move=>n; apply: norm_bounded_cvg.
exists M; near=>J.
apply/(le_trans _ (PM (val @` J)%fset)).
rewrite !psum_seq_fsetE big_imfset// =>i j _ _; apply/val_inj.
apply/cvgrPdist_lt=>e egt0.
move: (summable_cvg (f := Summable.build SF))=>/cvgrPdist_lt/(_ _ (e2gt0 egt0))[S1/=] _ P2.
pose N2 := (\max_(i <- (h @` S1)%fset) i).+1.
exists N2=>// N/= PN.
move: (Pcn N)=>/cvgrPdist_lt/(_ _ (e2gt0 egt0))[S2/=] _ P4.
have Ph: forall i : S1, (h (val i) < N)%N.
move=>[i/= Pi]; apply: (leq_trans _ PN); rewrite/N2 ltnS.
have Phi: h i \in (h @` S1)%fset by apply/imfsetP; exists i.
rewrite big_seq_fsetE/= (bigmax_sup [`Phi]%fset)//.
pose hs := fun i : S1 => exist (fun j => (h j < N)%N) _ (Ph i) : {i : I | (h i < N)%N}.
pose S := ([fset hs i | i : S1] `|` S2)%fset.
have /P4 Q2: (S2 `<=` S)%fset by apply/fsubsetUr.
have /P2 Q3: (S1 `<=` (val @` S))%fset.
  apply/fsubsetP=>i Pi; apply/imfsetP.
  exists (hs [`Pi])%fset=>//=; rewrite !inE/=; apply/orP; left. 
  by apply/imfsetP; exists [`Pi]%fset.
apply/(norm_split Q3).
rewrite psum_seq_fsetE big_imfset/=; first by move=>i j _ _; apply/val_inj.
rewrite -psum_seq_fsetE; apply: Q2.
Unshelve. end_near.
Qed.

Lemma summable_sigma_nat_is_cvg (h : I -> nat) (F : I -> V) : summable F -> 
    cvg (sum (fun i : {i : I | (h i < n)%N} => F (val i)) @[n --> \oo])%classic.
Proof. by move/(summable_sigma_nat_cvg h)=>P1; apply/cvg_ex; exists (sum F). Qed.

Lemma summable_sigma_nat_lim (h : I -> nat) (F : I -> V) : summable F -> 
  lim (sum (fun i : {i : I | (h i < n)%N} => F (val i)) @[n --> \oo])%classic = sum F.
Proof. by move=>/(summable_sigma_nat_cvg h)/cvg_lim->. Qed.

End sum_sigma_cvg.

End Exports.

End Summable_Reindex.

Export Summable_Reindex.Exports.

Section SumE.
Import Summable.Exports HermitianTopology.
Local Open Scope ring_scope.
Context {R : realType} {C : extNumType R} .

Lemma sum_summableE {I J : choiceType} {V : completeNormedModType C} (f : I -> {summable J -> V}) j :
  cvg (psum f @ totally)%classic -> sum f j = sum (fun i => f i j).
Proof.
move=>/cvgrPdist_lt Pc1.
suff: (psum (fun i : I => f i j) @ totally --> sum f j)%classic.
by move=>/cvg_lim P1; symmetry; apply: P1.
apply/cvgrPdist_lt=>c cgt0.
near=>t. have: (`|sum f - psum f t| < c) by near: t; apply: Pc1.
apply/le_lt_trans/(le_trans _ (psum_norm_ler_norm (sum f - psum f t) [fset j]%fset)).
by rewrite psum1 /normf !summableE /psum summable_sumE.
Unshelve. end_near.
Qed.

Lemma sum_summable_soE_cvg {U : chsType} {I : choiceType} (f : I -> 'SO(U)) (v : 'End(U)) :
  cvg (psum f @ totally)%classic -> 
    (psum (fun i : I => f i v) @ totally --> sum f v)%classic.
Proof.
move=>/cvgrPdist_lt Pc1.
apply/cvgrPdist_lt=>c cgt0; case: (@eqP _ `|v| 0)=>[/normr0_eq0->|/eqP].
  by near=>t; rewrite /psum big1// =>[? _|]; rewrite ?linear0// addr0 normr0.
rewrite normr_eq0 -normr_gt0=>Pv; near=>t.
have: (`|sum f - psum f t| < c / `|v|) by near: t; apply/Pc1/divr_gt0.
rewrite ltr_pdivlMr//; apply/le_lt_trans/(le_trans _ (itnormP _ _));
by rewrite !soE.
Unshelve. all: end_near.
Qed.

Lemma sum_summable_soE_is_cvg {U : chsType} {I : choiceType} (f : I -> 'SO(U)) (v : 'End(U)) :
  cvg (psum f @ totally)%classic -> cvg (psum (fun i : I => f i v) @ totally)%classic.
Proof.
move=>/(sum_summable_soE_cvg (v := v)) H1.
by apply/cvg_ex; exists (sum f v).
Qed.

Lemma sum_summable_soE {U : chsType} {I : choiceType} (f : I -> 'SO(U)) (v : 'End(U)) :
  cvg (psum f @ totally)%classic -> sum f v = sum (fun i => f i v).
Proof.
move=>/(sum_summable_soE_cvg (v := v)) /cvg_lim P1.
by symmetry; apply: P1.
Qed.

Lemma sum_summable_lfunE_cvg {U : chsType} {I : choiceType} (f : I -> 'End(U)) (v : U) :
  cvg (psum f @ totally)%classic -> 
    (psum (fun i : I => f i v) @ totally --> sum f v)%classic.
Proof.
move=>/cvgrPdist_lt Pc1.
apply/cvgrPdist_lt=>c cgt0; case: (@eqP _ `|v| 0)=>[/normr0_eq0->|/eqP].
  by near=>t; rewrite /psum big1// =>[? _|]; rewrite ?linear0// addr0 normr0.
rewrite normr_eq0 -normr_gt0=>Pv; near=>t.
have: (`|sum f - psum f t| < c / `|v|) by near: t; apply/Pc1/divr_gt0.
rewrite ltr_pdivlMr//; apply/le_lt_trans/(le_trans _ (trfnormP _ _)).
by rewrite lfunE/= lfunE/= /psum sum_lfunE.
Unshelve. all: end_near.
Qed.

Lemma sum_summable_lfunE_is_cvg {U : chsType} {I : choiceType} (f : I -> 'End(U)) (v : U) :
  cvg (psum f @ totally)%classic -> cvg (psum (fun i : I => f i v) @ totally)%classic.
Proof.
move=>/(sum_summable_lfunE_cvg (v := v)) H1.
by apply/cvg_ex; exists (sum f v).
Qed.

Lemma sum_summable_lfunE {U : chsType} {I : choiceType} (f : I -> 'End(U)) (v : U) :
  cvg (psum f @ totally)%classic -> sum f v = sum (fun i => f i v).
Proof.
move=>/(sum_summable_lfunE_cvg (v := v)) /cvg_lim P1.
by symmetry; apply: P1.
Qed.

End SumE.

Section VDistr_SuperOp.
Import Bounded.Exports Summable.Exports VDistr.Exports HermitianTopology.
Variable (I : choiceType) (U V : chsType) (f : {vdistr I -> 'SO(U,V)}).

Lemma sum_dso_cptn : sum f \is cptn.
Proof. apply: itnorm_ge0_le1P. apply: vdistr_sum_ge0. apply: vdistr_sum_le1. Qed.
HB.instance Definition _ := isQOperation.Build _ _ (sum f) sum_dso_cptn.

Lemma psum_dso_cptn (A : {fset I}) : psum f A \is cptn.
Proof.
apply: itnorm_ge0_le1P; last first.
apply/(le_trans _ (vdistr_sum_le1 (s := f)))/itnorm_ge0_le.
1,3: apply: sumv_ge0=>??; apply: vdistr_ge0.
apply: psum_vdistr_lev_sum.
Qed.
HB.instance Definition _ A := isQOperation.Build _ _ (psum f A) (psum_dso_cptn A).
Variable (A : {fset I}).

Lemma dso_cptn i : f i \is cptn.
Proof. by move: (psum_dso_cptn [fset i]%fset); rewrite psum1. Qed.
HB.instance Definition _ i := isQOperation.Build _ _ (f i) (dso_cptn i).

End VDistr_SuperOp.

Import VDistr.Exports.

HB.instance Definition _ (U V : chsType) (F : finType) := gen_eqMixin 'TN(F;U,V).
HB.instance Definition _ (U V : chsType) (F : finType) := gen_choiceMixin 'TN(F;U,V).

HB.instance Definition _ (U V : chsType) (F : finType) := gen_eqMixin 'QM(F;U,V).
HB.instance Definition _ (U V : chsType) (F : finType) := gen_choiceMixin 'QM(F;U,V).

Inductive cmd_ : Type :=
  | abort_
  | skip_
  | assign_ {t} of cvar t & expr_ (eval_ctype t) (* deterministic assignment *)
  | random_ {t : cType} of cvar t & dexpr (eval_ctype t) (* random sampling *)
  | cond_       of bexpr & cmd_ & cmd_ (* if condition *)
  | while_      of bexpr & cmd_        (* while condition *)
  | for_ {t}    of cvar t & expr_ (seq (eval_ctype t)) & cmd_ (* for loop *)
  | seqc_       of cmd_ & cmd_ 
  | initial_ {t} of qreg t & sexpr (eval_qtype t) (* initialization *)
  | unitary_ {t} of qreg t & uexpr (eval_qtype t) (* unitary transformation *)
  | measure_ {tc tq : qType} of cvar (QType tc) & 
      qreg tq & (mexpr (eval_qtype tc) (eval_qtype tq)). (* quantum measurement *)

Module Import CQWhileSyn.

Reserved Notation "'If' e 'then' c1 'else' c2"
  (at level 65, right associativity).
Reserved Notation "'If' e 'then' '{' c1 '}' 'else' '{' c2 '}'"
  (at level 65, right associativity, 
  format "'[v' 'If'  e  'then'  '{' '/' '['     c1 ']' '/' '}'  'else'  '{' '/' '['     c2 ']' '/' '}' ']'").
Reserved Notation "'IfT' e 'then' c1"
  (at level 65, right associativity).
Reserved Notation "'IfT' e 'then' '{' c1 '}'"
  (at level 65, right associativity, format
     "'[v' 'IfT'  e  'then'  '{' '/' '['     c1 ']' '/' '}' ']'").
Reserved Notation "'For' x 'in' e 'Do' c"
  (at level 65, right associativity).
Reserved Notation "'For' x 'in' e 'Do' '{' c '}'"
  (at level 65, right associativity, format
     "'[v' 'For'  x  'in'  e  'Do'  '{' '/' '['     c ']' '/' '}' ']'").
Reserved Notation "'For' x 'Do' c"
  (at level 65, right associativity).
Reserved Notation "'For' x 'Do' '{' c '}'"
  (at level 65, right associativity, format
     "'[v' 'For'  x  'Do'  '{' '/' '['     c ']' '/' '}' ']'").
Reserved Notation "'While' e 'Do' c"
  (at level 65, no associativity).
Reserved Notation "'While' e 'Do' '{' c '}' "
  (at level 65, no associativity, format
     "'[v' 'While'  e  'Do'  '{' '/' '['     c ']' '/' '}' ']'").
Reserved Notation "x <<- e"
  (at level 65, e at level 70, no associativity, format "x  <<-  e").
Reserved Notation "x <$- d"
  (at level 65, d at level 70, no associativity, format "x  <$-  d").
Reserved Notation "[{ x }] <*- d"
  (at level 65, x custom reg, d at level 70, no associativity, format "[{ x }]  <*-  d").
Reserved Notation "[{ x }] <:- d"
  (at level 65, x custom reg, d at level 70, no associativity, format "[{ x }]  <:-  d").
Reserved Notation "x <m- M [{ y }]"
  (at level 65, y custom reg, M at level 70, no associativity, format "x  <m-  M [{ y }]").
Reserved Notation "c1 ;; c2"
  (at level 74, left associativity, format "'[' c1  ;;  '/' '[' c2 ']' ']'").

Notation "'If' e 'then' c1 'else' c2"
  := (cond_ e%X c1%V c2%V) (only parsing) : vsyn_scope.
Notation "'If' e 'then' '{' c1 '}' 'else' '{' c2 '}'"
  := (cond_ e%X c1%V c2%V) : vsyn_scope.
Notation "'IfT' e 'then' c1"
  := (cond_ e%X c1%V skip_) (only parsing) : vsyn_scope.
Notation "'IfT' e 'then' '{' c1 '}'"
  := (cond_ e%X c1%V skip_) : vsyn_scope.
Notation "'While' e 'Do' c"
  := (while_ e%X c%V) (only parsing) : vsyn_scope.
Notation "'While' e 'Do' '{' c '}'"
  := (while_ e%X c%V) : vsyn_scope.
Notation "'For' x 'in' e 'Do' c"
  := (for_ x%V e%X c%V) (only parsing) : vsyn_scope.
Notation "'For' x 'in' e 'Do' '{' c '}'"
  := (for_ x%V e%X c%V) : vsyn_scope.
Notation "'For' x 'in' e 'Do' c"
  := (for_ x%V e%X c%V) (only parsing) : vsyn_scope.
Notation "'For' x 'in' e 'Do' '{' c '}'"
  := (for_ x%V e%X c%V) : vsyn_scope.
Notation "'For' x 'Do' c"
  := (for_ x%V ((index_enum _)%:CS)%X c%V) (only parsing) : vsyn_scope.
Notation "'For' x 'Do' '{' c '}'"
  := (for_ x%V ((index_enum _)%:CS)%X c%V) : vsyn_scope.
Notation "x <<- e"
  := (assign_ x%V e%X) : vsyn_scope.
Notation "x <$- d"
  := (random_ x%V d%X) : vsyn_scope.
Notation "c1 ;; c2"
  := (seqc_ c1%V c2%V) (format "'[v' c1  ';;' '/' c2 ']'"): vsyn_scope.
Notation "[{ x }] <*- d"
  := (unitary_ x d%X): vsyn_scope.
Notation "[{ x }] <:- d"
  := (initial_ x d%X): vsyn_scope.
Notation "x <m- M [{ y }]"
  := (measure_ x y M%X): vsyn_scope.

End CQWhileSyn.
(* question: logic: what is the predicate? expression, or coq formulas? *)

(* since context is a finmap, so there's always a finite system that implement 
   the program, thus we only assume the quantum system is finite, and we can 
   use lift... *)


(******************************************************************************)
(*               Basic constructs : sunit, sdlet, sdistr, smeas               *)
(******************************************************************************)
Section Basic_Constructs.
Import Bounded.Exports Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope fset_scope.
Implicit Type (I J : choiceType).

(************************              sunit             **********************)
Definition sunit_def I (U : zmodType) (i : I) (v : U) :=
  fun j => if j == i then v else 0%R.

Lemma sunit_summable_subproof I (R : numFieldType) (U : normedZmodType R) (i : I) (v : U) :
  summable (sunit_def i v).
Proof.
exists `|v|; near=>J.
rewrite -[J](fsetID [fset i]) psumU ?fdisjointID// -[ `|v|]addr0 lerD//.
have <-: psum (fun x : I => `|sunit_def i v x|) [fset i]%fset = `|v|.
by rewrite psum1/sunit_def eqxx.
apply: psum_ler=>[? _|]; [exact: normr_ge0 | exact: fsubsetIr].
rewrite /psum big1// /sunit_def /normf =>[[]]/= j; 
by rewrite !inE=>/andP[]/negPf->; rewrite normr0.
Unshelve. end_near.
Qed.

HB.instance Definition _ I (R : numFieldType) (U : normedZmodType R) (i : I) (v : U) :=
  isSummable.Build _ _ _ (sunit_def i v) (sunit_summable_subproof i v).

Lemma sunit_sum I (U : completeNormedModType C) (i : I) (v : U) :
  sum (sunit_def i v) = v.
Proof.
move: (summable_cvg (f := (sunit_def i v)))=>/=.
apply: (closed_cvg (fun x : U => x = v) (@closed_eq _ _ v)).
exists [fset i] =>//= x/=/fsetIidPr Px.
rewrite -[x](fsetID [fset i]) psumU ?fdisjointID// Px.
rewrite psum1 /sunit_def eqxx /psum big1 ?addr0 ?qo_isqoP//= =>[[j/=]].
by rewrite !inE=>/andP[]/negPf->.
Qed.

Lemma sunit_vdistr_ge0 I (U V : chsType) (i : I) (v : 'QO(U,V)) :
  forall j : I, (0 : 'SO) ⊑ sunit_def i (v : 'SO) j.
Proof. by intros=>/=; rewrite /sunit_def; case: eqP=>// _; apply: qoge0. Qed.

Lemma sunit_vdistr_sum_le1 I (U V : chsType) (i : I) (v : 'QO(U,V)) :
  `| sum (sunit_def i (v : 'SO)) | <= 1.
Proof. rewrite sunit_sum; apply/itnorm_qo. Qed.

HB.instance Definition _ I U V i v := Summable_isVDistr.Build _ _ _ (sunit_def _ _)
  (@sunit_vdistr_ge0 I U V i v) (sunit_vdistr_sum_le1 i v).

Definition sunit_vdistr I (U V : chsType) (i : I) (v : 'QO(U,V)) 
  : {vdistr I -> 'SO(U,V)} := sunit_def i (v : 'SO).

(************************              sdlet             **********************)
Definition sdlet_def I J (U : completeNormedModType C) (f : I -> J) 
  (g : {summable I -> U}) : J -> U :=
    fun j => sum (fun i => sunit_def (f i) (g i) j).

Lemma sdlet_summable_subproof I J U f g : summable (@sdlet_def I J U f g).
Proof.
exists `|g|; near=>O.
rewrite/sum/psum (eq_bigr (fun i => lim ((fun A : {fset I} => 
  `|\sum_(i0 : A) sunit_def (f (val i0)) (g (val i0)) (val i)|) @ totally)%classic)); last first.
rewrite -(lim_sum_fset (F := totally) (J:=O) (f := (fun (i : J) (A : {fset I}) => 
`|\sum_(i0 : A) sunit_def (f (val i0)) (g (val i0)) i| ))); last first.
apply: etlim_le_near; last first.
  near=>Si. rewrite fct_sumE.
  apply: (le_trans (y := \sum_(j : O)\sum_(i : Si) `|sunit_def (f (val i)) (g (val i)) (val j)|)).
  apply: ler_sum=>/= j _; apply: (le_trans (ler_norm_sum _ _ _))=>//.
  rewrite exchange_big/=; apply: (le_trans (y := psum (fun x : I => `|g x|) Si)).
  apply: ler_sum=>/= i _.
  case E: (f (fsval i) \in O); last first.
  rewrite big1// =>[[]]j Pj _/=; rewrite/sunit_def; case: eqP=>eqj; last by rewrite normr0.
  by move: eqj Pj E=>->->.
  rewrite (bigD1 [` E])//= big1=>[[]j Pj/=|].
  by rewrite -(inj_eq (val_inj))/=/sunit_def=>/negPf->; rewrite normr0.
  by rewrite addr0 /sunit_def eqxx.
  apply: psum_norm_ler_norm.
apply: (is_cvg_sum (f := (fun (i : O) (A : {fset I}) => 
  `|\sum_(i0 : A) sunit_def (f (val i0)) (g (val i0)) (val i)| )))=>+ _.
1,2: move=>o; apply: is_cvg_norm.
3: move=>o _; symmetry; apply: lim_norm.
all: suff: cvg (psum (fun i0 : I => sunit_def (f i0) (g i0) (val o)) @ totally)%classic by [].
all: apply: norm_bounded_cvg; exists `|g|; near=>Si;
  apply: (le_trans (y := psum (fun x : I => `|g x|) Si));
  last by apply: psum_norm_ler_norm.
all: by apply: ler_sum=>/=i _; rewrite/sunit_def /normf; case: eqP=>[//|]; rewrite normr0.
Unshelve. all: end_near.
Qed.

HB.instance Definition _ I J (U : completeNormedModType C) (f : I -> J) 
  (g : {summable I -> U}) := isSummable.Build _ _ _ (sdlet_def f g)
  (sdlet_summable_subproof f g).

Lemma sdlet_vdistr_ge0 I J (U V : chsType) (f : I -> J) 
  (g : {vdistr I -> 'SO(U,V)}) : forall j, (0 : 'SO) ⊑ sdlet_def f g j.
Proof.
move=>j; apply: lim_gev_near; last first.
  near=>S; rewrite/psum sumv_ge0//==>K _; rewrite/sunit_def; case: eqP=>// _; apply: vdistr_ge0.
apply: norm_bounded_cvg; exists `|g : {summable _ -> _}|; near=>Si;
apply: (le_trans (y := psum (fun x : I => `|g x|) Si)); last by apply: psum_norm_ler_norm.
by apply: ler_sum=>/=i _; rewrite/sunit_def /normf; case: eqP=>[//|]; rewrite normr0.
Unshelve. all: end_near.
Qed.

Lemma sunit_psum I (R : numFieldType) (U : normedZmodType R) (i : I) (v : U) (J : {fset I}):
  psum (sunit_def i v) J = if (i \in J) then v else 0.
Proof.
case E: (i \in J).
rewrite -{1}[J](fsetID [fset i]) psumU ?fdisjointID//.
have ->: J `&` [fset i] = [fset i] by apply/fsetIidPr/fsubsetP=>x; rewrite inE=>/eqP->.
rewrite psum1 {1}/sunit_def eqxx.
all: rewrite /psum big1 /sunit_def ?addr0// =>[[j/=+ _]]; rewrite ?inE.
by move=>/andP[]/negPf->.
by move=>P; case: eqP=>// E1; move: E1 E P=>->->.
Qed.

Lemma sunit_def_mapE I (R : numFieldType) (U V : normedZmodType R) (f : U -> V) (i : I) (v : U) :
  f 0 = 0 -> (fun j => f (sunit_def i v j)) = sunit_def i (f v).
Proof. by move=>f0; apply/funext=>j; rewrite/sunit_def; case: eqP. Qed.

Lemma sdlet_sum I J (U : completeNormedModType C) (f : I -> J) 
  (g : {summable I -> U}) : sum (sdlet_def f g) = sum g.
Proof.
rewrite -pseries2_exchange_lim; last by f_equal; apply/funext=>i; rewrite sunit_sum.
exists `| g | =>Si Sj; apply: (le_trans _ (psum_norm_ler_norm g Si)).
by apply: ler_sum=>/=i _; rewrite sunit_def_mapE ?normr0// /normf sunit_psum; case: (_ \in Sj).
Qed.

Lemma sdlet_vdistr_sum_le1 I J (U V : chsType) (f : I -> J) 
  (g : {vdistr I -> 'SO(U,V)}) : `| sum (sdlet_def f g) | <= 1.
Proof. by rewrite sdlet_sum; apply: vdistr_sum_le1. Qed.

HB.instance Definition _ I J U V f g := Summable_isVDistr.Build _ _ _ (sdlet_def _ _)
  (@sdlet_vdistr_ge0 I J U V f g) (sdlet_vdistr_sum_le1 f g).

Definition sdlet_vdistr I J (U V : chsType) (f : I -> J) 
  (g : {vdistr I -> 'SO(U,V)}) : {vdistr J -> 'SO(U,V)} := sdlet_def f g.

(************************             sdistr             **********************)
(*                       project random sampling to vdistr                    *)
Definition sdistr_def I (U : chsType) (mu : Distr I) :=
  (fun i : I => mu i *: \:1 : 'SO(U)).

Lemma sdistr_summable_subproof I U mu : summable (@sdistr_def I U mu).
Proof.
exists `|\:1 : 'SO(U)|; near=>J; rewrite/psum.
under eq_bigr do rewrite /normf normrZ.
rewrite -mulr_suml -[X in _ <= X]mul1r ler_wpM2r// (eq_bigr (fun i : J=>mu (val i))).
by move=>??; rewrite ger0_norm// ge0_mu.
apply: (le_trans _ (sum_le1_mu mu)). apply: le_psum_mu.
Unshelve. end_near.
Qed.

HB.instance Definition _ I (U : chsType) (mu : Distr I) :=
  isSummable.Build _ _ _ (sdistr_def U mu) (sdistr_summable_subproof U mu).

Lemma sdistr_vdistr_ge0 I (U : chsType) (mu : Distr I)
  : forall j, (0 : 'SO) ⊑ sdistr_def U mu j.
Proof. by move=>j; rewrite/sdistr_def scalev_ge0// ?leso01// ge0_mu. Qed.

Lemma sdistr_sum I (U : chsType) (mu : Distr I) :
  sum (sdistr_def U mu) = (sum mu) *: \:1.
Proof.
rewrite/sum -limZl. apply: summable_cvg.
suff ->: psum (sdistr_def U mu) = fun x => psum mu x *: \:1. by [].
by apply/funext=>x; rewrite /psum/sdistr_def scaler_suml.
Qed.

Lemma sdistr_vdistr_sum_le1 I (U : chsType) (mu : Distr I) 
  : `| sum (sdistr_def U mu) | <= 1.
Proof. by rewrite sdistr_sum normrZ itnorm_qc mulr1 ger0_norm ?sum_ge0_mu// sum_le1_mu. Qed.

HB.instance Definition _ I U mu := Summable_isVDistr.Build _ _ _ (sdistr_def _ _)
  (@sdistr_vdistr_ge0 I U mu) (sdistr_vdistr_sum_le1 U mu).

Definition sdistr I (U : chsType) (mu : Distr I) : 
  {vdistr I -> 'SO(U)} := sdistr_def U mu.

(* move *)
Lemma fin_dom_summable (I : finType) (K : numFieldType) (V : normedZmodType K) 
  (f : I -> V) : summable f.
Proof.
exists (\sum_(i : fsetT) `|f (val i)|); near=>J; rewrite/psum.
rewrite -!(big_seq_fsetE _ _ xpredT (fun i : I => `|f i|))/=.
rewrite -(fsetUCr J) big_fsetU/= ?fdisjointXC// lerDl sumr_ge0//.
Unshelve. end_near.
Qed.
Lemma fin_dom_sum (I : finType) (K : numFieldType) (V : normedModType K) 
  (f : I -> V) : sum f = \sum_i f i.
Proof.
apply: cvg_lim. apply: norm_hausdorff.
apply: cvg_near_cst; exists fsetT=>//= x/=.
by rewrite fsubTset=>/eqP->; rewrite/psum -big_fsetT.
Qed.

(************************             smeas              **********************)
(*                               for measurement                              *)
Definition smeas_def (U V : chsType) (I : finType) (f : I -> 'Hom(U, V)) :=
  (fun i : I => elemso f i ).

Lemma smeas_summable_subproof U V (I : finType) f : summable (@smeas_def U V I f).
Proof. exact: fin_dom_summable. Qed.

HB.instance Definition _ (U V : chsType) (I : finType) (f : I -> 'Hom(U, V)) :=
  isSummable.Build _ _ _ (smeas_def f) (smeas_summable_subproof f).

Lemma smeas_sum (U V : chsType) (I : finType) (f : I -> 'Hom(U, V)) :
  sum (smeas_def f) = \sum_i (elemso f i).
Proof. exact: fin_dom_sum. Qed.

Lemma smeas_vdistr_ge0 (U V : chsType) (I : finType) (f : I -> 'Hom(U, V))
  : forall j, (0 : 'SO) ⊑ smeas_def f j.
Proof. by move=>j; rewrite/smeas_def cp_geso0. Qed.

Lemma smeas_vdistr_sum_le1 (U V : chsType) (I : finType) (f : 'TN(I;U,V))
  : `| sum (smeas_def f) | <= 1.
Proof. by rewrite smeas_sum elemso_sum itnorm_qo. Qed.

HB.instance Definition _ (U V : chsType) (I : finType) (f : 'TN(I;U,V)) := 
  Summable_isVDistr.Build _ _ _ (smeas_def f)
  (smeas_vdistr_ge0 f) (smeas_vdistr_sum_le1 f).

Definition smeas (U V : chsType) (I : finType) (f : 'TN(I;U,V))
  : {vdistr I -> 'SO(U,V)} := smeas_def f.

End Basic_Constructs.

Section Denotational_Semantics.
Import Bounded.Exports Summable.Exports VDistr.Exports ExtNumTopology HermitianTopology.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope fset_scope.

Variant semType (Ii Io : choiceType) (U V : chsType) := 
  SemType of Ii -> {vdistr Io -> 'SO(U,V)}.

Definition semtype_val Ii Io U V (s : semType Ii Io U V) := 
  let: SemType g := s in g.

Coercion semtype_val : semType >-> Funclass.

Lemma semtypeP Ii Io U V (f g : semType Ii Io U V) :
  f = g <-> f =1 g.
Proof. by split=>[->//|]; move: f g=>[]f[]g/=/funext ->. Qed.

Lemma sem_bounded_subproof Ii Io U V (m : semType Ii Io U V) :
  bounded (fun i : Ii => m i : {summable Io -> 'SO(U,V)}).
Proof.
move: (normv_lbounded (@choinorm U V))=>[]/=c cgt0 Pc.
exists (1/c)=>i; rewrite {1}/Num.norm/=.
apply: etlim_le_near. apply: summable_norm_is_cvg.
near=>J; rewrite/psum/= mulrC ler_pdivlMl// mulr_sumr.
apply: (le_trans (y := \sum_(i0 : J) choinorm (m i (fsval i0)))).
  by apply ler_sum=>j _; rewrite /normf/=.
rewrite -choinorm_ge0_sum; first by move=>/=j; apply: vdistr_ge0.
apply/choinorm_qoP/itnorm_ge0_le1P.
rewrite sumv_ge0=>[/=j _|//]; apply: vdistr_ge0.
apply: (le_trans _ (vdistr_sum_le1 (s := m i))).
apply: itnorm_ge0_le; first by rewrite sumv_ge0=>[/=j _|//]; apply: vdistr_ge0.
by apply: (le_trans _ (psum_vdistr_lev_sum (m i) J)).
Unshelve. end_near.
Qed.

Definition sem_bounded Ii Io U V (m : semType Ii Io U V) := 
  Bounded.build (sem_bounded_subproof m).

Coercion sem_bounded : semType >-> Bounded.type.
Canonical sem_bounded.

Definition sunit (I J : choiceType) (U V : chsType) (f : I -> 'QO(U,V)) 
  (g : I -> J) : semType I J U V
    := SemType (fun i : I => sunit_vdistr (g i) (f i)).

Definition sdlet (I T J : choiceType) (U V : chsType) (f : I -> T -> J)
  (g : I -> {vdistr T -> 'SO(U,V)}) : semType I J U V
    := SemType (fun i : I => sdlet_vdistr (f i) (g i)).

(*   composition  *)
Definition slet_def (Ii Im Io : choiceType) (U V W: chsType) 
  (mu1 : semType Ii Im U V) (mu2 : semType Im Io V W) (i : Ii) :=
    fun j : Io => sum (fun m : Im => (mu2 m j) :o (mu1 i m)).

Lemma slet_norm_ubound (Ii Im Io : choiceType) (U V W: chsType) :
  exists M0 : C, 0 < M0 /\ forall (mu1 : semType Ii Im U V) 
    (mu2 : semType Im Io V W) (i : Ii) (So : {fset Io}) (Sm : {fset Im}), 
      psum (fun j : Io => psum (fun m : Im => `|mu2 m j :o mu1 i m|) Sm) So <= M0.
Proof.
move: (normv_lbounded (@choinorm U V))=>[]/=c1 c1gt0 Pc1.
move: (normv_lbounded (@choinorm V W))=>[]/=c2 c2gt0 Pc2.
exists (1/c1/c2); split=>[|mu1 mu2 i So Sm]; first by do ! apply/divr_gt0=>//; apply: ltr01.
rewrite !ler_pdivlMr// !mulr_suml /psum.
apply: (le_trans (y := \sum_(o : So)\sum_(m : Sm) choinorm (mu2 (val m) (val o)) * choinorm (mu1 i (val m)))).
apply/ler_sum=>o _; rewrite -!ler_pdivlMr// !mulr_suml; apply/ler_sum=>m _.
apply/(le_trans (itnormM _ _)); rewrite ler_pdivlMr// mulrC mulrA ler_pdivlMr// -[_ * c1]mulrA [_ * c1]mulrC.
by apply: ler_pM=>//; apply/mulr_ge0=>//; apply/ltW.
rewrite exchange_big/=. under eq_bigr do rewrite -mulr_suml -choinorm_cp_sum/= psumE.
apply/(le_trans (y := choinorm (psum (mu1 i) Sm))); last by apply: choinorm_qo.
rewrite choinorm_cp_sum/=; apply/ler_sum=>m _. apply/ler_piMl.
apply: normv_ge0. apply: choinorm_qo.
Qed.

Lemma slet_norm_uboundW (Ii Im Io : choiceType) (U V W: chsType) 
  (mu1 : semType Ii Im U V) (mu2 : semType Im Io V W) (i : Ii) :
    exists M0 : C, forall (So : {fset Io}) (Sm : {fset Im}), 
      psum (fun j : Io => psum (fun m : Im => `|mu2 m j :o mu1 i m|) Sm) So <= M0.
Proof. by move: (slet_norm_ubound Ii Im Io U V W)=>[Mc [_ Pc]]; exists Mc. Qed.

Lemma slet_summable_subproof Ii Im Io U V W mu1 mu2 i :
  summable (@slet_def Ii Im Io U V W mu1 mu2 i).
Proof.
by rewrite/slet_def; 
move: (pseries_ubounded_cvg (slet_norm_uboundW mu1 mu2 i))=>[] _ [] _ [] + _.
Qed.

HB.instance Definition _ Ii Im Io U V W mu1 mu2 i :=
  isSummable.Build _ _ _ _ (@slet_summable_subproof Ii Im Io U V W mu1 mu2 i).

Lemma slet_vdistr_ge0 Ii Im Io U V W mu1 mu2 i
  : forall j, (0 : 'SO) ⊑ @slet_def Ii Im Io U V W mu1 mu2 i j.
Proof.
move=>j; rewrite /slet_def; apply: lim_gev_near.
by move: (pseries_ubounded_cvg (slet_norm_uboundW mu1 mu2 i))=>[] _ []/(_ j) + _.
near=>Mm; apply: sumv_ge0=>m _; apply: cp_geso0.
Unshelve. end_near.
Qed.

Lemma slet_vdistr_sum_le1 Ii Im Io U V W mu1 mu2 i : 
  `| sum (@slet_def Ii Im Io U V W mu1 mu2 i) | <= 1.
Proof.
apply: itnorm_qoP.
suff: (\forall K \near totally, psum (slet_def mu1 mu2 i) K \is cptn).
move=> /(closed_cvg (fun x => x \is cptn)) P.
by move: (summable_cvg (f := slet_def mu1 mu2 i))=>/=; apply/P/closed_isqo.
near=>K.
rewrite /psum/slet_def -lim_sum_apply; last first.
suff: cvg (\sum_(i0 : K) psum (fun m : Im => mu2 m (val i0) :o mu1 i m) J @[J --> totally])%classic.
suff: (\forall J \near totally, \sum_(i0 : K) psum (fun m : Im => mu2 m (val i0) :o mu1 i m) J \is cptn).
move=> /(closed_cvg (fun x => x \is cptn)) P.
by apply/P/closed_isqo.
near=>J. apply: itnorm_ge0_le1P; last first.
apply: itnorm_ler_psd; last first.
move=>x Px. rewrite !psd_trfnorm//.
rewrite sum_soE psdlfE sumv_ge0// =>j _; rewrite sum_soE sumv_ge0// =>k _.
by rewrite -psdlfE; apply: cp_psdP.
apply: (le_trans (y := \Tr ((psum (mu1 i) J) x))); last by rewrite mul1r; apply: qo_trlfE.
rewrite/psum exchange_big/= !sum_soE !linear_sum/= ler_sum// =>j _.
by rewrite -linear_sumlz/= soE psumE; apply: qo_trlfE; apply: cp_psdP.
rewrite -geso0_cpE.
1,2: apply: sumv_ge0=>??; apply: sumv_ge0=>??; apply: cp_geso0.
apply: is_cvg_sum_apply.
1,2: by move=>j _; move: (pseries_ubounded_cvg (slet_norm_uboundW mu1 mu2 i))=>[] _ [] /(_ (val j)) + _.
Unshelve. all: end_near.
Qed.

HB.instance Definition _ Ii Im Io U V W mu1 mu2 i :=
  Summable_isVDistr.Build _ _ _ (slet_def _ _ _) 
  (@slet_vdistr_ge0 Ii Im Io U V W mu1 mu2 i) (slet_vdistr_sum_le1 mu1 mu2 i).

Definition slet_vdistr (Ii Im Io : choiceType) (U V W: chsType) 
  (mu1 : semType Ii Im U V) (mu2 : semType Im Io V W) (i : Ii)
  : {vdistr Io -> 'SO(U,W)} := slet_def mu1 mu2 i.

Definition slet (Ii Im Io : choiceType) (U V W: chsType) 
  (mu1 : semType Ii Im U V) (mu2 : semType Im Io V W) : semType Ii Io U W
  := SemType (slet_vdistr mu1 mu2).

Lemma sletA (Ii Im1 Im2 Io : choiceType) (U V W X: chsType) 
  (mu1 : semType Ii Im1 U V) (mu2 : semType Im1 Im2 V W) 
  (mu3 : semType Im2 Io W X) :
  slet (slet mu1 mu2) mu3 = slet mu1 (slet mu2 mu3).
Proof.
apply/semtypeP=>mi/=. apply/vdistrP=>mj/=.
rewrite /slet_def/=/slet_def.
have ->: (fun m : Im2 => mu3 m mj :o sum (fun m0 : Im1 => mu2 m0 m :o mu1 mi m0))
  = (fun m : Im2 => sum (fun m0 : Im1 => (mu3 m mj :o mu2 m0 m) :o mu1 mi m0)).
  apply/funext=>j; symmetry; rewrite/sum.
  have P: (fun x => psum (fun m0 : Im1 => (mu3 j mj :o mu2 m0 j) :o mu1 mi m0) x)
    =1 ((fun x => mu3 j mj :o x) \o (fun x => psum (fun m0 : Im1 => mu2 m0 j :o mu1 mi m0) x))%FUN.
    by move=>x/=; rewrite/psum linear_sumr; apply eq_bigr=>??/=; rewrite comp_soA.  
  rewrite (eq_lim _ P); apply: linearr_lim.
  by move: (pseries_ubounded_cvg (slet_norm_uboundW mu1 mu2 mi))=>[] _ [] /(_ j) + _.
rewrite pseries2_exchange_lim.
  move: (normv_lbounded (@choinorm U V))=>[]/=c1 c1gt0 Pc1.
  move: (slet_norm_ubound Im1 Im2 Io V W X)=>[c2 [c2gt0 /(_ mu2 mu3) Pc2]].
  exists (c2 / c1)=>So Sm.
  rewrite/psum exchange_big/=.
  apply: (le_trans (y := \sum_(j : Sm) c2 * `|mu1 mi (val j)|)).
  apply/ler_sum=>j _.
  apply: (le_trans (y := \sum_(i : So) `|(mu3 (val i) mj :o mu2 (val j) (val i))| * `|mu1 mi (val j)|)).
  apply/ler_sum=>??; apply/itnormM.
  by rewrite -mulr_suml ler_wpM2r//; move: (Pc2 (val j) [fset mj]%fset So); rewrite psum1.
  rewrite -mulr_sumr ler_wpM2l//; first by apply/ltW.
  rewrite -div1r ler_pdivlMr//.
  apply/(le_trans (y := choinorm (psum (mu1 mi) Sm))); last by apply: choinorm_qo.
  by rewrite mulr_suml /psum choinorm_cp_sum/= ler_sum// =>??; rewrite mulrC Pc1.
f_equal; apply/funext=>i; rewrite/sum.
have P: (fun x => psum (fun x : Im2 => (mu3 x mj :o mu2 i x) :o mu1 mi i) x)
  =1 ((fun x => x :o mu1 mi i) \o (fun x => psum (fun m : Im2 => mu3 m mj :o mu2 i m) x))%FUN
  by move=>x/=; rewrite/psum linear_sumlz.
rewrite (eq_lim _ P); apply: linearl_lim.
by move: (pseries_ubounded_cvg (slet_norm_uboundW mu2 mu3 i))=>[] _ [] /(_ mj) + _.
Qed.

(* cpo : deal with while loop *)
(* Notation cmem := qreg_cmem__canonical__choice_Choice. *)

Definition abort_sem {I : choiceType} {U : chsType} : semType I I U U := 
  sunit (fun => abortso _ _) id.
Lemma abort_semE {I : choiceType} {U : chsType} (i j : I) :
  abort_sem i j = 0 :> 'SO(U).
Proof. by rewrite/= /sunit_def; case: eqP. Qed.
Definition skip_sem {I : choiceType} {U : chsType} : semType I I U U := 
  sunit (fun => \:1) id.
Lemma skip_semE {I : choiceType} {U : chsType} (i j : I) :
  skip_sem i j = if (j == i) then \:1 else 0 :> 'SO(U).
Proof. by []. Qed.
Definition if_sem {U : chsType} (be : bexpr) 
  (s1 s2 : semType cmem cmem U U) : semType cmem cmem U U := 
  SemType (fun m : cmem => if (esem be m) then s1 m else s2 m).
Lemma if_semE {U : chsType} (be : bexpr) (s1 s2 : semType cmem cmem U U) (m : cmem) :
  (if_sem be s1 s2 m) = if (esem be m) then s1 m else s2 m.
Proof. by []. Qed.

Lemma slet1l (I : choiceType) (U : chsType) (c : semType I I U U) :
  slet skip_sem c = c.
Proof.
apply/semtypeP=>i; apply/vdistrP=>j/=.
rewrite/slet_def (fin_supp_sum (S := [fset i]%fset)).
by move=>k; rewrite inE skip_semE=>/negPf->; rewrite comp_so0r.
by rewrite psum1 skip_semE eqxx comp_so1r.
Qed.

Lemma slet1r (I : choiceType) (U : chsType) (c : semType I I U U) :
  slet c skip_sem = c.
Proof.
apply/semtypeP=>i; apply/vdistrP=>j/=.
rewrite/slet_def (fin_supp_sum (S := [fset j]%fset)).
by move=>k; rewrite inE skip_semE eq_sym=>/negPf->; rewrite comp_so0l.
by rewrite psum1 skip_semE eqxx comp_so1l.
Qed.

Lemma eq_sum (I : choiceType) (K : numFieldType) (R : normedModType K) (f g : I -> R) :
  f =1 g -> sum f = sum g.
Proof. by move=>/funext->. Qed.

Lemma slet_sum (Ii Im Io : choiceType) (U V W : chsType)
  (J : Type) (r : seq J) (P : pred J)
  (mu1 : J -> semType Ii Im U V) (mu2 : J -> semType Im Io V W) 
  (i : Ii) (o : Io) :
  \sum_(j <- r | P j) slet (mu1 j) (mu2 j) i o 
  = sum (fun m : Im => \sum_(j <- r | P j) (mu2 j m o :o mu1 j i m)).
Proof.
rewrite/=/slet_def/sum -lim_sum_apply=>[j _|].
by move: (pseries_ubounded_cvg (slet_norm_uboundW (mu1 j) (mu2 j) i))=>[] _ []/(_ o) + _.
by apply: eq_lim=>S; rewrite/psum exchange_big.
Qed.

Lemma slet_fold (Ii Im Io : choiceType) (U V W : chsType) (mu1 : semType Ii Im U V) 
  (mu2 : semType Im Io V W) (i : Ii) (o : Io) :
    slet_def mu1 mu2 i o = slet mu1 mu2 i o.
Proof. by []. Qed.

Definition sem_lim (I J : choiceType) (U V : chsType) (f : nat -> semType I J U V) := 
  SemType (fun i : I => vdlim (FF := eventually_filter) (fun t : nat => f t i)).

Lemma comp_so_ge0 (U V W : chsType) (f : 'SO(U,V)) (g : 'SO(W,U)) :
  (0 : 'SO) ⊑ f -> (0 : 'SO) ⊑ g -> (0 : 'SO) ⊑ f :o g.
Proof.
move=>/geso0_cpP Pf/geso0_cpP Pg; apply/geso0_cpP.
by move: (comp_so_cp (CPMap_Build Pf) (CPMap_Build Pg)).
Qed.

Lemma leso_comp2l (U V W : chsType) (f g : 'SO(U,V)) (h : 'SO(W,U)) :
  (0 : 'SO) ⊑ h -> f ⊑ g -> f :o h ⊑ g :o h.
Proof. by move=>Ph; rewrite -subv_ge0=>Pg; rewrite -subv_ge0 -linearBl/= comp_so_ge0. Qed.

Lemma leso_comp2r (U V W : chsType) (h : 'SO(U,V)) (f g : 'SO(W,U)) :
  (0 : 'SO) ⊑ h -> f ⊑ g -> h :o f ⊑ h :o g.
Proof. by move=>Ph; rewrite -subv_ge0=>Pg; rewrite -subv_ge0 -linearBr/= comp_so_ge0. Qed.

Lemma leso_comp (U V W : chsType) (f g : 'SO(U,V)) (x y : 'SO(W,U)) :
  (0 : 'SO) ⊑ f -> (0 : 'SO) ⊑ x -> 
    f ⊑ g -> x ⊑ y -> f :o x ⊑ g :o y.
Proof.
move=>P1 P2 P3 P4; apply/(le_trans (y := f :o y)).
by apply: leso_comp2r. apply: leso_comp2l=>[|//]. by apply/(le_trans (y := x)).
Qed.

Lemma slet_in_out_summable (Ii Im Io : choiceType) (U V W : chsType) 
  (f : semType Ii Im U V) (g : semType Im Io V W) i o :
    summable (fun m : Im => g m o :o f i m).
Proof.
move: (slet_norm_uboundW f g i)=>[c /(_ [fset o]) Pc].
exists c. by near=>J; move: (Pc J); rewrite psum1.
Unshelve. end_near.
Qed.

Lemma slet_lim (Ii Im Io : choiceType) (U V W : chsType) 
  (f : nat -> semType Ii Im U V) (g : nat -> semType Im Io V W) :
  (forall i, nondecreasing_seq (fun t => f t i)) ->
  (forall i, nondecreasing_seq (fun t => g t i)) ->
  sem_lim (fun n => slet (f n) (g n)) = slet (sem_lim f) (sem_lim g).
Proof.
pose lf i := vdlim (FF := eventually_filter) (fun t : nat => f t i).
pose lg i := vdlim (FF := eventually_filter) (fun t : nat => g t i).
move=>Pf Pg; apply/semtypeP=>i; apply/vdistrP=>o/=.
pose h (t : nat) := (fun m : Im => g t m o :o f t i m).
rewrite vdlimEE.
  move: (vdistr_norm_ubound (I := Io) (@choinorm_ge0_add U W))=>[c [cgt0 Pc]].
  apply/(snondecreasing_norm_is_cvgn (@choinorm_ge0_add _ _) (b := c))=>[m n Pmn|t//].
  apply/levdP=>j; apply: lev_lim.
  apply: (summable_cvg (f := Summable.build (slet_in_out_summable (f m) (g m) i j))).
  apply: (summable_cvg (f := Summable.build (slet_in_out_summable (f n) (g n) i j))).
  move=>S; apply/lev_sum=>??; apply: leso_comp.
  1,2: apply: vdistr_ge0. by apply/levdP1/Pg. by apply/levdP1/Pf.
have Shc : cvg (Summable.build (slet_in_out_summable (f t) (g t) i o) @[t --> \oo])%classic.
  move: (slet_norm_ubound Ii Im Io U V W)=>[c [cgt0 Pc1]].
  apply/(snondecreasing_norm_is_cvgn (@choinorm_ge0_add _ _) (b := c)).
  move=>m n Pmn. apply/lesP=>im/=.
  apply: leso_comp. 1,2: apply: vdistr_ge0. by apply/levdP1/Pg. by apply/levdP1/Pf.
  move=>t; rewrite/Num.Def.normr/=.
  apply: etlim_le. apply: summable_norm_is_cvg.
  move=>S. move: (Pc1 (f t) (g t) i [fset o] S).
  by rewrite psum1.
rewrite (summable_sum_lim (f := fun t : nat => Summable.build (slet_in_out_summable (f t) (g t) i o)))=>[//|].
rewrite /slet_def; f_equal; apply/funext=>m.
rewrite -summableE_lim=>[//|].
rewrite !vdlimEE. 1,2: by apply/(vdnondecreasing_is_cvgn (@choinorm_ge0_add _ _)).
rewrite so_comp_lim=>[||//]; apply: summableE_is_cvg;
by apply/(vdnondecreasing_is_cvgn (@choinorm_ge0_add _ _)).
Qed.

Lemma sem_lim_cst (Ii Io : choiceType) (U V : chsType) (f : semType Ii Io U V) :
  sem_lim (fun => f) = f.
Proof.
apply/semtypeP=>i; apply/vdistrP=>j/=; rewrite vdlimEE.
apply: is_cvg_cst. by rewrite lim_cst.
Qed.

Lemma slet_liml (Ii Im Io : choiceType) (U V W : chsType) 
  (f : nat -> semType Ii Im U V) (g : semType Im Io V W) :
  (forall i, nondecreasing_seq (fun t => f t i)) ->
  sem_lim (fun n => slet (f n) g) = slet (sem_lim f) g.
Proof. by move=>Pf; rewrite -{2}[g]sem_lim_cst -slet_lim// =>?. Qed.

Lemma slet_limr (Ii Im Io : choiceType) (U V W : chsType) 
  (g : nat -> semType Im Io V W) (f : semType Ii Im U V) :
  (forall i, nondecreasing_seq (fun t => g t i)) ->
  sem_lim (fun n => slet f (g n)) = slet f (sem_lim g).
Proof. by move=>Pf; rewrite -{2}[f]sem_lim_cst -slet_lim// =>?. Qed.

Fixpoint while_sem_iter (U : chsType) (be : bexpr) 
  (c : semType cmem cmem U U) (n : nat) : semType cmem cmem U U := 
  match n with
  | 0 => sunit (fun => abortso _ _) id
  | S n => if_sem be (slet c (while_sem_iter be c n)) skip_sem
  end.

Definition while_sem (U : chsType) (be : bexpr) (c : semType cmem cmem U U) :=
  sem_lim (while_sem_iter be c).

Fixpoint while_sem_incr (U : chsType) (be : bexpr) 
  (c : semType cmem cmem U U) (n : nat) : semType cmem cmem U U := 
  match n with
  | 0 => skip_sem
  | S n => slet (if_sem be c abort_sem) (while_sem_incr be c n)
  end.

Lemma while_sem_incrED (U : chsType) (be : bexpr) (c : semType cmem cmem U U) n :
  (while_sem_incr be c n.+1) = slet (if_sem be c abort_sem) (while_sem_incr be c n).
Proof. by []. Qed.

Lemma whileso_sem_incrE (U : chsType) (be : bexpr) (c : semType cmem cmem U U) n :
  (while_sem_incr be c n.+1) = slet (while_sem_incr be c n) (if_sem be c abort_sem).
Proof.
elim: n=>[|n IH]; first by rewrite/= slet1r slet1l.
by rewrite while_sem_incrED {1}IH while_sem_incrED !sletA.
Qed.

Lemma while_sem_iter_incrEx (U : chsType) (be : bexpr) (c : semType cmem cmem U U) n x y :
  (while_sem_iter be c n x y) = 
  \sum_(i < n) slet (while_sem_incr be c i) (if_sem be abort_sem skip_sem) x y.
Proof.
elim: n x=>[x|n IH x]; first by rewrite big_ord0 /= /sunit_def /sum; case: eqP.
rewrite big_ord_recl slet1l/=; case E: (esem be x); last first.
  rewrite big1 ?addr0// =>i _; rewrite slet_fold sletA/=/slet_def.
  under eq_sum do rewrite if_semE E abort_semE comp_so0r.
  by rewrite summable_sum_cst0.
rewrite abort_semE add0r.
under eq_bigr do rewrite slet_fold sletA.
rewrite slet_sum.
under eq_sum do rewrite -linear_sumlz if_semE E.
rewrite/= /slet_def; f_equal; apply/funext=>m. f_equal.
by rewrite IH; apply eq_bigr=>i _; rewrite -/(slet_def _ _ _ _).
Qed.

Lemma while_sem_iter_homo (U : chsType) (be : bexpr) (c : semType cmem cmem U U) i : 
  nondecreasing_seq (fun n => while_sem_iter be c n i).
Proof.
move=>m n Pmn; apply/lesP=>j/=.
rewrite !while_sem_iter_incrEx.
rewrite (big_ord_widen _ (fun k => slet (while_sem_incr be c k) (if_sem be abort_sem skip_sem) i j) Pmn).
rewrite [X in _ ⊑ X](bigID (fun i : 'I_n => (i < m)%N))/= levDl.
by rewrite sumv_ge0// =>??; rewrite vdistr_ge0.
Qed.

Lemma while_sem_is_cvg (U : chsType) (be : bexpr) (c : semType cmem cmem U U) i :
  cvgn (fun n => while_sem_iter be c n i : {summable _ -> _}).
Proof.
apply/(vdnondecreasing_is_cvgn (@choinorm_ge0_add _ _))/while_sem_iter_homo.
Qed.

Lemma while_sem_limE (U : chsType) (be : bexpr) (c : semType cmem cmem U U) i :
  limn (fun n => while_sem_iter be c n i : {summable _ -> _}) = 
    while_sem be c i.
Proof. by symmetry; apply/vdlimE/while_sem_is_cvg. Qed.

Lemma while_sem_limEE (U : chsType) (be : bexpr) (c : semType cmem cmem U U) i o :
  limn (fun n => while_sem_iter be c n i o) = while_sem be c i o.
Proof.
move: (while_sem_limE be c i)=>/summableP/(_ o)<-.
rewrite summableE_lim//; apply: while_sem_is_cvg.
Qed.

Lemma while_sem_limEEE (U : chsType) (be : bexpr) (c : semType cmem cmem U U) i o q :
  limn (fun n => while_sem_iter be c n i o q) = while_sem be c i o q.
Proof.
move: (while_sem_limEE be c i o)=>/superopP/(_ q)<-.
rewrite so_liml//; apply: summableE_is_cvg; apply: while_sem_is_cvg.
Qed.

Lemma while_sem_limE_shiftn (U : chsType) (be : bexpr) (c : semType cmem cmem U U) k i :
  limn (fun n => while_sem_iter be c (n+k) i : {summable _ -> _}) = 
    while_sem be c i.
Proof.
move: (@while_sem_is_cvg _ be c i).
rewrite -while_sem_limE -(cvg_shiftn k)/=. by apply: cvg_lim.
Qed.

Lemma while_sem_limE_shiftS (U : chsType) (be : bexpr) (c : semType cmem cmem U U) i :
  limn (fun n => while_sem_iter be c n.+1 i : {summable _ -> _}) = 
    while_sem be c i.
Proof.
by move: (@while_sem_is_cvg _ be c i); rewrite -while_sem_limE -cvg_shiftS; apply: cvg_lim.
Qed.

Lemma while_sem_lim_shiftn (U : chsType) (be : bexpr) (c : semType cmem cmem U U) k :
  while_sem be c = sem_lim (fun n => while_sem_iter be c (n+k)).
Proof.
apply/semtypeP=>i; rewrite/sem_lim/=; apply/vdistrP/summableP.
rewrite [LHS]vdlimE. apply: while_sem_is_cvg.
rewrite [RHS]vdlimE ?while_sem_limE_shiftn ?while_sem_limE=>[|//].
by move: (@while_sem_is_cvg _ be c i); rewrite -while_sem_limE -{1}(cvg_shiftn k).
Qed.

Lemma while_sem_lim_shiftS (U : chsType) (be : bexpr) (c : semType cmem cmem U U) :
  while_sem be c = sem_lim (fun n => while_sem_iter be c n.+1).
Proof. by rewrite (while_sem_lim_shiftn be c 1); f_equal; apply/funext=>i/=; rewrite addn1. Qed.

Lemma while_sem_ub (U : chsType) (be : bexpr) (c : semType cmem cmem U U) n i : 
  while_sem_iter be c n i ⊑ while_sem be c i.
Proof. apply/(vdnondecreasing_cvg_le (@choinorm_ge0_add _ _))/while_sem_iter_homo. Qed.

Lemma while_sem_least (U : chsType) (be : bexpr) (c : semType cmem cmem U U) i x : 
  (forall n, while_sem_iter be c n i ⊑ x) -> while_sem be c i ⊑ x.
Proof.
move=>P. rewrite levdEsub -while_sem_limE.
apply: lim_les_nearF. apply: while_sem_is_cvg.
by apply: nearW.
Qed.

Lemma while_sem_false (U : chsType) (be : bexpr) (c : semType cmem cmem U U) i : 
  esem be i = false -> while_sem be c i = skip_sem i.
Proof.
move=>Pf. apply/vdistrP/summableP. rewrite -while_sem_limE_shiftS.
have ->: (fun n => while_sem_iter be c n.+1 i : {summable _ -> _}) = (fun => skip_sem i).
by apply/funext; elim=>[/=|n/=<-]; rewrite/= Pf.
by rewrite lim_cst.
Qed.

Lemma while_sem_fixpoint (U : chsType) (be : bexpr) (c : semType cmem cmem U U) : 
  while_sem be c = if_sem be (slet c (while_sem be c)) skip_sem.
Proof.
apply/semtypeP=>i.
case E: (esem be i); last by rewrite (while_sem_false _ E) if_semE E.
rewrite {1}while_sem_lim_shiftS if_semE E /while_sem -slet_limr/= ?E//.
apply: while_sem_iter_homo.
Qed.

Local Notation setT := finset.setT.

Notation sem_type := (semType cmem cmem 'H[msys]_setT 'H[msys]_setT).
(* Definition abort_sem : sem_type := sunit (fun => abortso_qoType _ _) id. *)
(* Definition skip_sem : sem_type := sunit (fun => idso_qoType _) id. *)
Definition assign_sem {t : cType} (x : cvar t) (e : expr_ (eval_ctype t)) : sem_type 
  := sunit (fun => \:1) (fun m => m.[x <- esem e m])%M.
Definition initial_sem {t : qType} (q : qreg t) (phi : sexpr (eval_qtype t)) : sem_type 
  := sunit (fun m => liftfso (initialso (tv2v q (esem phi m)))) id.
Definition unitary_sem {t : qType} (q : qreg t) (u : uexpr (eval_qtype t)) : sem_type 
  := sunit (fun m : cmem => liftfso (formso
    (tf2f q q (esem u m)))) id.
Definition random_sem {t : cType} (x : cvar t) (e : dexpr (eval_ctype t)) : sem_type :=
  sdlet (fun (m : cmem) (y : (eval_ctype t)) => m.[x <- y])%M
  (fun (m : cmem) => sdistr _ (esem e m)).
Definition measure_sem {tc tq : qType} (x : cvar (QType tc)) (q : qreg tq) 
  (me : mexpr (eval_qtype tc) (eval_qtype tq)) : sem_type :=
  sdlet (fun (m : cmem) (y : (eval_ctype ((QType tc)))) => m.[x <- y])%M
  (fun (m : cmem) => smeas (liftf_fun (tm2m q q (esem me m)))).
Definition seqc_sem (s1 s2 : sem_type) : sem_type := slet s1 s2.
(* Definition cond_sem (be : bexpr) (s1 s2 : sem_type) : sem_type := 
  SemType (fun m : cmem => if (esem be m) then s1 m else s2 m). *)
Definition for_sem {t : cType} (x : cvar t) (e : expr_ (seq (eval_ctype t))) 
  (c : sem_type) : sem_type := SemType (fun m : cmem => 
    ((\big[seqc_sem/skip_sem]_(i <- esem e m)
      seqc_sem (sunit (fun => \:1) (fun m => m.[x <- i])%M) c) m)).
(* Definition while_sem  *)

Fixpoint sem_aux (c : cmd_) : sem_type :=
  match c with
  | abort_ => abort_sem
  | skip_ => skip_sem
  | assign_ _ x e => assign_sem x e
  | random_ _ x e => random_sem x e
  | cond_ be c1 c2 => if_sem be (sem_aux c1) (sem_aux c2)
  | while_ be c => while_sem be (sem_aux c)
  | for_ _ x e c => for_sem x e (sem_aux c)
  | seqc_ c1 c2 => seqc_sem (sem_aux c1) (sem_aux c2)
  | initial_ _ q phi => initial_sem q phi
  | unitary_ _ q u => unitary_sem q u
  | measure_ _ _ x q me => measure_sem x q me
  end. (* quantum measurement *)

End Denotational_Semantics.

(******************************************************************************)
(* We first give the operational semantics (transition rules) for cqwhile     *)
(* Next, we define the induced denotational semantics, opsum, i.e., summation *)
(* over all possible transition route                                         *)
(* Finally, we prove that opsum is equivalent to the denotational semantics   *)
(* defined above, which, by definition, have the structure representation     *)
(******************************************************************************)

Section Operational_Semantics.
Import Bounded.Exports Summable.Exports VDistr.Exports HermitianTopology.
Import ExtNumTopology.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope fset_scope.

Notation Hq := 'H[msys]_finset.setT.

(* transition rule , corresponds to finite computation *)
Inductive trans_rule : 
  cmd_ -> (cmem * 'End(Hq)) -> (cmem * 'End(Hq)) -> Type :=
  | T_skip (i : cmem * 'End(Hq)) : 
    trans_rule skip_ i i
  | T_assign {t} (x : cvar t) (e : expr_ (eval_ctype t)) (i : cmem * 'End(Hq)) :
    trans_rule (assign_ x e) i ((i.1.[x <- esem e i.1])%M, i.2)
  | T_random {t} (v : (eval_ctype t)) (x : cvar t) (e : dexpr (eval_ctype t)) 
    (i : cmem * 'End(Hq)) : 
    trans_rule (random_ x e) i ((i.1.[x <- v])%M, (esem e i.1 v) *: i.2)
  (* if true, if false *)
  | T_cond1 (e : bexpr) (c1 c2 : cmd_) (i o : cmem * 'End(Hq)) (He : esem e i.1) 
    (HI : trans_rule c1 i o) :
    trans_rule (cond_ e c1 c2) i o
  | T_cond2 (e : bexpr) (c1 c2 : cmd_) (i o : cmem * 'End(Hq)) (He : ~~ (esem e i.1)) 
    (HI : trans_rule c2 i o) :
    trans_rule (cond_ e c1 c2) i o
  (* while false, while true *)
  | T_while0 (e : bexpr) (c : cmd_) (i : cmem * 'End(Hq)) (He : ~~ (esem e i.1)) :
    trans_rule (while_ e c) i i
  | T_while1 (e : bexpr) (c : cmd_) (i o : cmem * 'End(Hq)) (He : esem e i.1) 
    (HI : trans_rule (seqc_ c (while_ e c)) i o) :
    trans_rule (while_ e c) i o
  (* seq None, we enforce to finish the first part *)
  (* in order to make the application unique *)
  | T_seqc (c1 c2 : cmd_) (i m o : cmem * 'End(Hq)) 
    (HI1 : trans_rule c1 i m) (HI2 : trans_rule c2 m o) :
    trans_rule (seqc_ c1 c2) i o
  (* | T_seqc1 (c1 c2 cm: cmd_) (i o : cmem * 'End(Hq)) 
    (Hi : trans_rule (Some c1, i) (Some cm, o)) :
    trans_rule (Some (seqc_ c1 c2), i) (Some (seqc_ cm c2), o) *)
  | T_initial {t} (q : qreg t) (s : sexpr (eval_qtype t)) (i : cmem * 'End(Hq)) :
    trans_rule (initial_ q s) i
      (i.1, liftfso (initialso (tv2v q (esem s i.1))) i.2)
  | T_unitary {t} (q : qreg t) (u : uexpr (eval_qtype t)) (i : cmem * 'End(Hq)) :
    trans_rule (unitary_ q u) i
      (i.1, liftfso (formso (tf2f q q (esem u i.1))) i.2)
  | T_measure {tc tq : qType} (v : eval_qtype tc) (x : cvar (QType tc)) (q : qreg tq) 
    (m : mexpr (eval_qtype tc) (eval_qtype tq)) (i : cmem * 'End(Hq)) :
    trans_rule (measure_ x q m) i 
      ((i.1.[x <- v])%M, liftfso (elemso (tm2m q q (esem m i.1)) v) i.2)
  (* for, evaluate the seq, then unfold for *)
  | T_for {t : cType} (x : cvar t) (e : expr_ (seq (eval_ctype t))) (c : cmd_)
    (i o : cmem * 'End(Hq)) 
    (HI : trans_rule (\big[seqc_/skip_]_(i <- esem e i.1) (seqc_ (assign_ x i%:CS) c)) i o) :
    trans_rule (for_ x e c) i o.

(* since transition rule is not a choiceType (due to universe inconsistancy) *)
(* we define a simpler type trans_route which only record the rules rather than cmd *)
Inductive trans_route : Type :=
  | TR_skip
  | TR_assign
  | TR_random {t} (v : (eval_ctype t)) 
  (* if true, if false *)
  | TR_cond1 (r : trans_route)
  | TR_cond2 (r : trans_route)
  | TR_while0
  | TR_while1 (r : trans_route)
  | TR_seqc (r1 r2 : trans_route)
  | TR_initial
  | TR_unitary
  | TR_measure {tc : qType} (v : eval_qtype tc)
  | TR_for (r : trans_route).

HB.instance Definition _ := gen_eqMixin trans_route.
HB.instance Definition _ := gen_choiceMixin trans_route.

Fixpoint route_size (r : trans_route) : nat :=
  match r with
  | TR_skip | TR_assign | TR_random _ _ | TR_while0 | TR_initial | TR_unitary | TR_measure _ _ => 1
  | TR_cond1 r => (route_size r).+1
  | TR_cond2 r => (route_size r).+1
  | TR_while1 r => (route_size r).+1
  | TR_seqc r1 r2 => ((route_size r1) + (route_size r2)).+1
  | TR_for r => (route_size r).+1
  end.

Lemma route_size_ind (P : trans_route -> Prop) :
  (forall n, (forall r, (route_size r < n)%N -> P r) -> 
    forall r, route_size r = n -> P r) -> forall r, P r.
Proof.
move=>IH r.
have [n Pn]: exists n, route_size r = n by exists (route_size r).
by elim/ltn_ind: n r Pn=>n Pn; apply/IH=>r Pr; apply/(Pn _ Pr).
Qed.

Definition cast_ctype (t t' : cType) (E : t = t') (v : eval_ctype t) : eval_ctype t' :=
  let: erefl in _ = t' := E return eval_ctype t' in v.

Definition cast_qtype (t t' : qType) (E : t = t') (v : eval_qtype t) : eval_qtype t' :=
  let: erefl in _ = t' := E return eval_qtype t' in v.

(* given a route and cmd, we evaluate the output if possible *)
Fixpoint eval_route (r : trans_route) (c : cmd_) 
  (i : cmem * 'End(Hq)) : option (cmem * 'End(Hq)) :=
  match r,c with
    | TR_skip, skip_ => Some i
    | TR_assign, assign_ t x e => Some ((i.1.[x <- esem e i.1])%M, i.2)
    | TR_random t v , random_ t' x e => 
        match asboolP (t = t') with
        | ReflectT Q => Some ((i.1.[x <- cast_ctype Q v])%M, (esem e i.1 (cast_ctype Q v)) *: i.2)
        | ReflectF Q => None
        end
    | TR_cond1 r, cond_ e c1 c2 =>
        if (esem e i.1) then eval_route r c1 i
        else None
    | TR_cond2 r, cond_ e c1 c2 =>
        if ~~ (esem e i.1) then eval_route r c2 i
        else None
    | TR_while0, while_ e c =>
        if ~~ (esem e i.1) then Some i
        else None
    | TR_while1 r, while_ e c =>
        if (esem e i.1) then eval_route r (seqc_ c (while_ e c)) i
        else None
    | TR_seqc r1 r2, seqc_ c1 c2 =>
        match (eval_route r1 c1 i) with
        | Some m => eval_route r2 c2 m
        | None => None
        end
    | TR_initial, initial_ t q s =>
        Some (i.1, liftfso (initialso (tv2v q (esem s i.1))) i.2)
    | TR_unitary, unitary_ t q u =>
        Some (i.1, liftfso (formso (tf2f q q (esem u i.1))) i.2)
    | TR_measure tc v, measure_ tc' tq x q m =>
        match asboolP (tc = tc') with
        | ReflectT Q => Some ((i.1.[x <- cast_qtype Q v])%M, 
            liftfso (elemso (tm2m q q (esem m i.1)) (cast_qtype Q v)) i.2)
        | ReflectF Q => None
        end
    | TR_for r, for_ t x e c =>
        eval_route r (\big[seqc_/skip_]_(i <- esem e i.1) (seqc_ (assign_ x i%:CS) c)) i
    | _, _ => None
  end.

Ltac exactltac := try (intros; match goal with 
  | [ H : is_true ((0 : 'End(Hq)) ⊑ ?x) |- is_true ((0 : 'End(Hq)) ⊑ ?x) ] => exact H end).

Lemma eval_route_ge0 (r : trans_route) (c : cmd_) (mi : cmem) (qi : 'End(Hq)) :
  0%:VF ⊑ qi -> 0%:VF ⊑ oapp snd qi (eval_route r c (mi,qi)).
Proof.
move: c r mi qi.
have E_seqc1 c1 c2 r1 r2 :
    (forall mi qi, 0%:VF ⊑ qi -> 0%:VF ⊑ oapp snd qi (eval_route r1 c1 (mi, qi))) ->
    (forall mi qi, 0%:VF ⊑ qi -> 0%:VF ⊑ oapp snd qi (eval_route r2 c2 (mi, qi))) ->
    (forall mi qi, 0%:VF ⊑ qi -> 0%:VF ⊑ oapp snd qi (eval_route (TR_seqc r1 r2) (c1 ;; c2)%V (mi, qi))).
  move=>/= H0 H1 mi qi H2; set n := (eval_route r1 c1 (mi, qi)).
  dependent destruction n; rewrite -x; exactltac.
  case: p x=>a b P. move: (H1 a b). set m := (eval_route r2 c2 (a,b)). 
  dependent destruction m=>/=; rewrite -x/=; exactltac.
  by apply; move: (H0 mi qi); rewrite -P/==>/(_ H2).
have E_skip r mi qi : 0%:VF ⊑ qi -> 
  0%:VF ⊑ oapp snd qi (eval_route r skip_ (mi, qi)) by case: r.
have E_assign c e r mi qi : 0%:VF ⊑ qi -> 
  0%:VF ⊑ oapp snd qi (eval_route r (c <<- e)%V (mi, qi)) by case: r.
have E_big T (s : seq T) (P : pred T) (F : T -> cmd_) :
  (forall i r mi qi, 0%:VF ⊑ qi -> 0%:VF ⊑ oapp snd qi (eval_route r (F i) (mi, qi))) ->
  (forall r mi qi, 0%:VF ⊑ qi -> 0%:VF ⊑ oapp snd qi (eval_route r (\big[seqc_/skip_]_(i <- s | P i) F i) (mi, qi))).
  elim: s=>[r mi qi H|a l H0 H1 r mi qi H2].
    by rewrite big_nil; apply: E_skip; apply: H.
  rewrite big_cons; case: (P a); last by apply: H0.
  case: r=>/=; exactltac=>r1 r2.
  apply/E_seqc1=>[||//]. apply: H1. apply/H0/H1.
move=>c; dependent induction c.
- case=>/=; exactltac.
- apply: E_skip.
- apply: E_assign.
- case=>/=; exactltac=>t0 v mi qi H0.
  case: asboolP=>[p|//]; case: t / p c e=>/= _ e; by rewrite scalev_ge0// ge0_mu.
- case=>/=; exactltac=>r mi qi H0.
  by case: (esem e mi)=>[|//=]; apply: IHc1.
  by case: (esem e mi)=>[//=|]; apply: IHc2.
- elim/route_size_ind=>n IH; case=>/=; exactltac.
  by intros; case: (~~ esem e mi).
  move=>r H0 mi qi H1; case E: (esem e mi)=>[|//].
  case: r H0=>/=; exactltac=>r1 r2 H2.
  apply: E_seqc1=>[||//]. apply: IHc.
  apply: IH; rewrite -H2 ltnS; apply/leqW/leq_addl.
- case=>/=; exactltac=>r mi qi H0. 
  apply: E_big; exactltac=>i r0 mi0 qi0.
  case: r0=>/=; exactltac=>r1 r2 H1.
  apply: E_seqc1. apply: E_assign. apply: IHc. apply: H1.
- case=>/=; exactltac=>r1 r2 mi qi H0.
  apply: E_seqc1. apply: IHc1. apply: IHc2. apply: H0.
- by case=>/=; exactltac=>mi qi H0; apply: cp_ge0.
- by case=>/=; exactltac=>mi qi H0; apply: cp_ge0.
- case=>/=; exactltac.
- by intros; case: asboolP; exactltac=>/= P; apply: cp_ge0.
Qed.

(* function that translate a rule to a route *)
Fixpoint trans_rule2route c i o (t : trans_rule c i o) : trans_route :=
  match t with
  | T_skip _ => TR_skip
  | T_assign _ _ _ _ => TR_assign
  | T_random _ v _ _ _ => TR_random v
  | T_cond1 _ _ _ _ _ _ t => TR_cond1 (trans_rule2route t)
  | T_cond2 _ _ _ _ _ _ t => TR_cond2 (trans_rule2route t)
  | T_while0 _ _ _ _ => TR_while0
  | T_while1 _ _ _ _ _ t => TR_while1 (trans_rule2route t)
  | T_seqc _ _ _ _ _ t1 t2 => TR_seqc (trans_rule2route t1) (trans_rule2route t2)
  | T_initial _ _ _ _ => TR_initial
  | T_unitary _ _ _ _ => TR_unitary
  | T_measure _ _ v _ _ _ _ => TR_measure v
  | T_for _ _ _ _ _ _ t => TR_for (trans_rule2route t)
  end.

(* function that translate a route to a rule *)
(* what remains to prove is that these two functions are pcancel & ocancel *)
(* i.e., they are one-to-one correspondent *)
Fixpoint trans_route2rule c i o (r : trans_route) : option (trans_rule c i o) :=
  match r, c with
  | TR_skip, skip_ => match asboolP (i = o) with
        | ReflectT E => let: erefl in _ = o := E return option (trans_rule _ i o) in Some (T_skip i)
        | ReflectF _ => None
        end
  | TR_assign, assign_ t x e => match asboolP (((i.1.[x <- esem e i.1])%M, i.2) = o) with
        | ReflectT E => let: erefl in _ = o := E return option (trans_rule _ i o) in Some (T_assign x e i)
        | ReflectF _ => None
        end
  | TR_random t v , random_ t' x e => match asboolP (t = t') with
            | ReflectT Q => 
              match asboolP (((i.1.[x <- cast_ctype Q v])%M, (esem e i.1 (cast_ctype Q v)) *: i.2) = o) with
              | ReflectT E => let: erefl in _ = o := E return option (trans_rule _ i o) in Some (T_random (cast_ctype Q v) x e i)
              | ReflectF _ => None
              end
            | ReflectF Q => None
            end
  | TR_cond1 r, cond_ e c1 c2 =>
            match asboolP (esem e i.1) with
            | ReflectT Q => match trans_route2rule c1 i o r with
                            | Some t => Some (T_cond1 c2 Q t)
                            | None => None
                            end
            | _ => None 
            end
  | TR_cond2 r, cond_ e c1 c2 =>
            match asboolP (~~ esem e i.1) with
            | ReflectT Q => match trans_route2rule c2 i o r with
                            | Some t => Some (T_cond2 c1 Q t)
                            | None => None
                            end
            | _ => None 
            end
  | TR_while0, while_ e c =>
            match asboolP (~~ esem e i.1) with
            | ReflectT Q => match asboolP (i = o) with
                            | ReflectT E => let: erefl in _ = o := E return option (trans_rule _ i o) in Some (T_while0 c Q)
                            | ReflectF _ => None
                            end
            | _ => None 
            end
  | TR_while1 r, while_ e c =>
            match asboolP (esem e i.1) with
            | ReflectT Q => match trans_route2rule (seqc_ c (while_ e c)) i o r with
                            | Some t => Some (T_while1 Q t)
                            | None => None
                            end
            | _ => None 
            end
  | TR_seqc r1 r2, seqc_ c1 c2 =>
            match eval_route r1 c1 i with
            | Some m => match trans_route2rule c1 i m r1 with
                        | Some t1 => match trans_route2rule c2 m o r2 with
                                     | Some t2 => Some (T_seqc t1 t2)
                                     | None => None
                                     end
                        | None => None
                        end
            | None => None
            end 
  | TR_initial, initial_ t q s => match asboolP ((i.1, liftfso (initialso (tv2v q (esem s i.1))) i.2) = o) with
        | ReflectT E => let: erefl in _ = o := E return option (trans_rule _ i o) in Some (T_initial q s i)
        | ReflectF _ => None
        end
  | TR_unitary, unitary_ t q u => match asboolP ((i.1, liftfso (formso (tf2f q q (esem u i.1))) i.2) = o) with
        | ReflectT E => let: erefl in _ = o := E return option (trans_rule _ i o) in Some (T_unitary q u i)
        | ReflectF _ => None
        end
  | TR_measure tc v, measure_ tc' tq x q m =>
        match asboolP (tc = tc') with
        | ReflectT Q => match asboolP (((i.1.[x <- cast_qtype Q v])%M, liftfso (elemso (tm2m q q (esem m i.1)) (cast_qtype Q v)) i.2) = o) with
                        | ReflectT E => let: erefl in _ = o := E return option (trans_rule _ i o) in Some (T_measure (cast_qtype Q v) x q m i)
                        | ReflectF _ => None
                        end
        | _ => None
        end
  | TR_for r, for_ t x e c =>
        match trans_route2rule (\big[seqc_/skip_]_(i <- esem e i.1) (seqc_ (assign_ x i%:CS) c)) i o r with
        | Some t => Some (T_for t)
        | None => None
        end
  | _, _ => None 
  end. 

Lemma eval_rule2route_correct c i o (t : trans_rule c i o) :
  eval_route (trans_rule2route t) c i = Some o.
Proof.
dependent induction t=>//=.
by case: asboolP=>[p|//]; rewrite eq_axiomK/=.
1,2,3,4: by rewrite He.
by rewrite IHt1.
by case: asboolP=>[p|//]; rewrite eq_axiomK.
Qed.

Lemma eval_route2rule_correct c i o (r : trans_route) :
  eval_route r c i = Some o ->
    exists t : trans_rule c i o, trans_route2rule c i o r = Some t.
Proof.
move: c i o; dependent induction r.
- by case=>// i o/= He; inversion He; exists (T_skip o); case: asboolP=>// p; rewrite eq_axiomK.
- by case=>// t x e i o/= He; inversion He; exists (T_assign x e i); case: asboolP=>// p; rewrite eq_axiomK.
- case=>// s x e i o/=; case: asboolP=>// p; case: s / p x e=>x e He; inversion He=>/=.
  by exists (T_random v x e i); case: asboolP=>// p; rewrite eq_axiomK.
- case=>// e c1 c2 i o/=; case: asboolP=>[p|/negP/negPf->//].
  by rewrite p=>/IHr[t ->]; exists (T_cond1 c2 p t).
- case=>// e c1 c2 i o/=; case: asboolP=>[p|/negP/negPf->//].
  by rewrite p=>/IHr[t ->]; exists (T_cond2 c1 p t).
- case=>// e c i o/=; case: asboolP=>[p|/negP/negPf->//].
  rewrite p=>He; inversion He as [H1]; case: o / H1 He => _; exists (T_while0 c p);
  by case: asboolP=>// p'; rewrite eq_axiomK.
- case=>// e c i o/=; case: asboolP=>[p|/negP/negPf->//].
  by rewrite p=>/IHr[t ->]; exists (T_while1 p t).
- case=>// c1 c2 i o/=; destruct (eval_route r1 c1 i) eqn: P=>//.
  by move: P=>/IHr1[t1 ->]/IHr2[t2 ->]; exists (T_seqc t1 t2).
- case=>//t q e i o/= He; inversion He; exists (T_initial q e i);
  by case: asboolP=>// p; rewrite eq_axiomK.
- case=>//t q e i o/= He; inversion He; exists (T_unitary q e i);
  by case: asboolP=>// p; rewrite eq_axiomK.
- case=>// tc1 tq x q e i o/=; case: asboolP=>// p; case: tc1 / p x e=>x e He.
  by inversion He=>/=; exists (T_measure v x q e i); case: asboolP=>// p; rewrite eq_axiomK.
- by case=>// t x e c i o/=/IHr[t1 ->]; exists (T_for t1).
Qed.

Lemma rule2routeK c i o : pcancel (@trans_rule2route c i o) (trans_route2rule c i o).
Proof.
move=>t; dependent induction t=>/=.
1,2,9,10: by case: asboolP=>// ?; rewrite eq_axiomK.
1,7: by do 2 (case: asboolP=>// ?; rewrite eq_axiomK/=).
1,2,4: by case: asboolP=>// p; rewrite IHt (Prop_irrelevance He p).
by case: asboolP=>// p; case: asboolP=>// ?; rewrite eq_axiomK (Prop_irrelevance He p).
by rewrite (eval_rule2route_correct t1) IHt1 IHt2.
by rewrite IHt.
Qed.

Lemma route2ruleK c i o : ocancel (trans_route2rule c i o) (@trans_rule2route c i o).
Proof.
move=>t; move: c i o; dependent induction t; case=>//=; intros.
by case: asboolP=>// p; case: o / p.
by case: asboolP=>// p; case: o / p.
by case: asboolP=>// p; case: t0 / p c e=> c e; case: asboolP=>// p; case: o / p.
by case: asboolP=>// p; move: (IHt c i o); case: (trans_route2rule c i o t)=>//=?->.
by case: asboolP=>// p; move: (IHt c0 i o); case: (trans_route2rule c0 i o t)=>//=?->.
by case: asboolP=>// p; case: asboolP=>// p1; case: o / p1.
case: asboolP=>// p; move: (IHt (seqc_ c (while_ e c)) i o);
by case: (trans_route2rule (seqc_ c (while_ e c)) i o)=>//=?->.
destruct (eval_route t1 c i) eqn: P=>//;
move: (eval_route2rule_correct P) (IHt1 c i p) (IHt2 c0 p o) =>[t Pt]; rewrite Pt/==> Pt1;
by case: (trans_route2rule c0 p o t2)=>//= ?->; rewrite Pt1.
by case: asboolP=>// p; case: o / p.
by case: asboolP=>// p; case: o / p.
by case: asboolP=>// p; case: tc0 / p c e=>c e/=; case: asboolP=>// p; case: o / p.
set c1 := \big[seqc_/skip_]_(i0 <- esem e i.1) (c <<- i0%:CS ;; c0)%V.
by move: (IHt c1 i o); destruct (trans_route2rule c1 i o t) eqn: P=>//=->.
Qed.

Definition states := {summable cmem -> 'End(Hq)}.

Definition opfun (c : cmd_) (mi : cmem) (qi : 'End(Hq)) r : {summable cmem -> 'End(Hq)} 
  := match eval_route r c (mi, qi) with
    | Some t => sunit_def t.1 t.2
    | None => 0
    end.

Definition opsum (c : cmd_) (mi : cmem) (qi : 'End(Hq)) 
  : {summable cmem -> 'End(Hq)} := sum (opfun c mi qi).

Local Notation "\`| f |" := (fun x => `|f x|) (at level 2).

Lemma sumE (I : choiceType) {K : numFieldType} {R : normedModType K}
   (x : I -> R) : lim ((psum x) @ totally)%classic = sum x.
Proof. by []. Qed.

Lemma sunit_normE (I : choiceType) (R : realType) (C : extNumType R)
  (U : normedModType C) (i : I) (u : U) :
  `|sunit_def i u : {summable _ -> _}| = `|u|.
Proof.
rewrite {1}/Num.Def.normr/=/summable_norm /normf sumE (fin_supp_sum (S := [fset i]%fset)).
by move=>j; rewrite inE/= /sunit_def=>/negPf->; rewrite normr0.
by rewrite psum1/= /sunit_def eqxx.
Qed.

Let opfun_summable (c : cmd_) (mi : cmem) (qi : 'End(Hq)) :=
  0%:VF ⊑ qi -> (forall S, psum \`|opfun c mi qi| S <= `|qi|).
Let opsum_norm_ub (c : cmd_) (mi : cmem) (qi : 'End(Hq)) :=
  0%:VF ⊑ qi -> `|opsum c mi qi| <= `|qi|.
Let op_sem_eq (c : cmd_) (mi : cmem) (qi : 'End(Hq)) :=
  forall mo, 0%:VF ⊑ qi -> opsum c mi qi mo = sem_aux c mi mo qi.
Let ind_hyp (c : cmd_) (mi : cmem) (qi : 'End(Hq)) :=
  opfun_summable c mi qi /\ op_sem_eq c mi qi.

Lemma opfun_summable_norm_ub (c : cmd_) (mi : cmem) (qi : 'End(Hq)) :
  opfun_summable c mi qi -> opsum_norm_ub c mi qi.
Proof.
move=>P1 Pq; rewrite /opsum.
have Ps: summable (opfun c mi qi). exists `|qi|. near=>S. by apply: P1.
rewrite (summablefE Ps). apply/(le_trans (summable_sum_ler_norm _)).
apply: etlim_le. apply: summable_norm_is_cvg. by apply: P1.
Unshelve. end_near.
Qed.

Lemma psum_lerG (I : choiceType) (T : numDomainType) (x : I -> T) (A B : {fset I}) :
  (forall i, i \in (B `\` A)%fset -> 0 <= x i) -> 
  (forall i, i \in (A `\` B)%fset -> x i <= 0) ->
    psum x A <= psum x B.
Proof.
move=>H1 H2.
rewrite -[A](fsetID B) -{3}[B](fsetID A) !psumU ?fdisjointID// fsetIC lerD2l.
apply/(le_trans (y := 0)); first rewrite -oppr_ge0 -psumN.
all: apply/sumr_ge0=>[[i/=+ _]].
by move=>/H2; rewrite fctE oppr_ge0. by move=>/H1.
Qed.

Lemma equal_OS_DS_skip (mi : cmem) (qi : 'End(Hq)) :
  ind_hyp skip_ mi qi.
Proof.
split=>[Pq S|mo].
  apply/(le_trans (y := psum \`| opfun skip_ mi qi | [fset TR_skip]%fset)).
  by apply: psum_lerG=>// i; rewrite !inE/opfun/==>/andP[]+ _; case: i=>//=; rewrite ?eqxx ?normr0.
  by rewrite psum1/opfun/= sunit_normE.
rewrite /opsum (fin_supp_sum (S := [fset TR_skip])) ?psum1//=.
by case; rewrite ?inE// eqxx. by rewrite /sunit_def; case: eqP; rewrite soE.
Qed. 

Lemma equal_OS_DS_assign (t : cType) (x : cvar t) 
  (e : expr_ (eval_ctype t)) (mi : cmem) (qi : 'End(Hq)) :
  ind_hyp (x <<- e)%V mi qi.
Proof.
split=>[Pq S|mo].
  apply/(le_trans (y := psum \`| opfun (x <<- e)%V mi qi | [fset TR_assign]%fset)).
  by apply: psum_lerG=>// i; rewrite !inE/opfun/==>/andP[]+ _; case: i=>//=; rewrite ?eqxx ?normr0.
  by rewrite psum1/opfun/= sunit_normE.
rewrite /opsum (fin_supp_sum (S := [fset TR_assign])) ?psum1//=.
by case; rewrite ?inE// eqxx. by rewrite /sunit_def; case: eqP; rewrite soE.
Qed.

Import Summable_Reindex.

Lemma equal_OS_DS_seqc (c1 c2: cmd_) :
  (forall mi qi, ind_hyp c1 mi qi) ->
  (forall mi qi, ind_hyp c2 mi qi) ->
  forall mi qi, ind_hyp (c1 ;; c2)%V mi qi.
move=>IH1 IH2.
pose h := (fun r => TR_seqc r.1 r.2).
pose h' := (fun r => match r with | TR_seqc r1 r2 => Some (r1,r2) | _ => None end).
have hK : pcancel h h'. by case.
have h'K : ocancel h' h. by case.
have PE: forall mi qi, 0%:VF ⊑ qi -> forall S1 S2,
  psum (fun r1 => psum (fun r2 => `|opfun (c1 ;; c2)%V mi qi (TR_seqc r1 r2)|) S2) S1 <= `|qi|.
  move=>/=mi qi Pq S1 S2. rewrite/opfun/=/psum.
  move: (IH1 mi qi)=>[]/(_ Pq S1)+ _; apply: le_trans.
  apply: ler_sum=>/= i _; rewrite /opfun.
  set a := (eval_route (fsval i) c1 (mi, qi)).
  dependent destruction a; rewrite -x.
  case: p x=>a b P/=; rewrite sunit_normE. move: (IH2 a b)=>[] P1 _. apply: P1.
  by move: (eval_route_ge0 (fsval i) c1 mi Pq); rewrite -P.
  by rewrite big1 normr0.
move=>mi qi.
have Pf : Hf h' (opfun (c1 ;; c2)%V mi qi) by case.
have Pfn : Hf h' \`| opfun (c1 ;; c2)%V mi qi|.
  by case=>//=; rewrite /opfun/= ?normr0.
have Q1: opfun_summable (c1 ;; c2)%V mi qi.
move=>Pq/= S; rewrite (psum_Sj hK h'K (TR_skip,TR_skip))//=.
set T := (Sj h' (TR_skip, TR_skip) S).
pose A := (fst @` T)%fset. pose B := (snd @` T)%fset.
apply/(le_trans (y := \sum_(i <- A)\sum_(j <- B) `|opfun (c1 ;; c2)%V mi qi (h (i, j))|)).
rewrite pair_big_dep_cond/= big_seq_fsetE/=. apply: psum_ler=>//.
apply/fsubsetP=>[[/=a b PT]]/=; rewrite !inE/= !andbT /A/B; apply/andP; split;
by apply/imfsetP; exists (a,b).
rewrite big_seq_fsetE; under eq_bigr do rewrite big_seq_fsetE.
by apply: PE.

split=>//; rewrite/op_sem_eq.
pose hx := (fun r : trans_route * trans_route => 
  match eval_route r.1 c1 (mi, qi) with
  | Some t => match eval_route r.2 c2 t with
            | Some t => sunit_def t.1 t.2
            | None => 0
            end
  | None => 0 end : {summable _ -> _}).
have Ph: (opfun (c1 ;; c2)%V mi qi \o h)%FUN = hx.
  by apply/funext=>[[r1 r2]]/=; rewrite/opfun/hx/=; case: (eval_route r1 c1 (mi, qi)).
move=>mo Pq.
have Pss: summable (opfun (c1 ;; c2)%V mi qi).
exists `|qi|. near=>J. by apply: Q1.
rewrite/opsum (@sum_reindex _ _ _ _ _ h h').
  1,2,3: by case.
  by apply/(reindex_summableP_simple (h' := h') _ _ (TR_skip,TR_skip)).
rewrite Ph.
have ->: sum hx = sum (fun r1 => sum (fun r2 => hx (r1,r2))).
  apply: pseries2_exchange_lim_pair.
  exists `|qi|=>/= Si Sj.
  apply/(le_trans _ (PE mi _ Pq Si Sj))/ler_sum=>i _; apply: ler_sum=>j _.
  by rewrite/hx/opfun/=; case: (eval_route (fsval i) c1 (mi, qi)).
rewrite sum_summableE.
  apply: norm_bounded_cvg. exists `|qi|. near=>J.
  apply/(le_trans _ (proj1 (IH1 mi qi) Pq J))/ler_sum=>i _.
  rewrite/hx/opfun/=/normf/=; set n := (eval_route (val i) c1 (mi, qi)).
  dependent destruction n; rewrite /opfun/= -x /normf; last by rewrite summable_sum_cst0.
  case: p x=>a1 a2/= P. rewrite-/(opfun c2 a1 a2) sunit_normE.
  apply: (opfun_summable_norm_ub (proj1 (IH2 a1 a2))).
  move: (eval_route_ge0 (fsval i) c1 mi Pq); rewrite -P; exactltac.
rewrite/hx/= (eq_sum (g := (fun i => match eval_route i c1 (mi, qi) with
| Some t => sem_aux c2 t.1 mo t.2 | None => 0 end))).
  move=>r1; set n := (eval_route r1 c1 (mi, qi)).
  dependent destruction n; rewrite -x.
  case: p x=>a1 a2/= P; apply: (proj2 (IH2 _ _)).
  move: (eval_route_ge0 r1 c1 mi Pq); rewrite -P/=; exactltac.
  by rewrite summable_sum_cst0 summableE.
rewrite/slet_def sum_summable_soE.
  apply: norm_bounded_cvg. 
  move: (slet_norm_uboundW (sem_aux c1) (sem_aux c2) mi)=>[M0/(_ [fset mo]%fset) PM].
  exists M0; near=>J; by move: (PM J); rewrite psum1.
under [in RHS]eq_sum do rewrite soE -(proj2 (IH1 mi qi) _ Pq).
rewrite [RHS](eq_sum (g := fun m => sum ((fun m r => 
  match eval_route r c1 (mi, qi) with
  | Some t => if t.1 == m then sem_aux c2 m mo t.2 else 0
  | None => 0 end) m))).
move=>m. rewrite sum_summableE.
  apply: norm_bounded_cvg; exists `|qi|; near=>J; apply: (proj1 (IH1 mi qi) Pq).
rewrite cvg_linear_sum.
  apply: norm_bounded_cvg; exists `|qi|; near=>J.
  apply/(le_trans _ (proj1 (IH1 mi qi) Pq J))/ler_sum=>i _.
  by move: (psum_norm_ler_norm (opfun c1 mi qi (val i)) [fset m]%fset); rewrite psum1.
f_equal. apply/funext=>r; rewrite/=.
set n := (eval_route r c1 (mi, qi)).
dependent destruction n; rewrite /opfun/= -x; last by rewrite summableE linear0.
by rewrite/=/sunit_def eq_sym; case: eqP=>//; rewrite linear0.
rewrite pseries2_exchange_lim.
  exists `|qi|=>Mm J; rewrite/psum exchange_big/=.
  apply/(le_trans _ (proj1 (IH1 mi qi) Pq J))/ler_sum=>i _.
  rewrite/opfun/=; set n := (eval_route (val i) c1 (mi, qi)).
  dependent destruction n; rewrite/= -x; last by rewrite !normr0 big1.
  rewrite sunit_normE; case E: (p.1 \in Mm).
  rewrite (bigD1 [` E])//= eqxx big1=>[j|].
  by rewrite -(inj_eq (val_inj))/= eq_sym=>/negPf ->; rewrite normr0.
  move: (eval_route_ge0 (val i) c1 mi Pq); rewrite -x/==>Pp.
  by rewrite addr0 !psd_trfnorm ?qo_trlfE ?cp_psdP ?psdlfE ?Pp.
  rewrite big1// =>[[j/= Pj _]]; case: eqP=>[Pe|]; last by rewrite normr0.
  by rewrite -Pe in Pj; rewrite Pj in E.
f_equal. apply/funext=>r.
case: (eval_route r c1 (mi, qi))=>[[a1 a2]|]; last by rewrite summable_sum_cst0.
rewrite/= (fin_supp_sum (S := [fset a1]%fset)) ?psum1 ?eqxx// =>i;
by rewrite inE eq_sym=>/negPf->.
Unshelve. all: end_near.
Qed.

Lemma sem_aux_big (T : Type) (r : seq T) (P : pred T) (c : T -> cmd_) :
  sem_aux (\big[seqc_/skip_]_(i <- r | P i) c i) = 
  \big[seqc_sem/skip_sem]_(i <- r | P i) sem_aux (c i).
Proof. by elim/big_rec2: _=>// i y1 y2 _ /= <-. Qed.

Lemma equal_OS_DS_big 
  (t : cType) (x : cvar t) (r : seq (eval_ctype t)) (c : cmd_) :
  (forall mi qi, ind_hyp c mi qi) ->
  forall mi qi, ind_hyp (\big[seqc_/skip_]_(i <- r) (x <<- i%:CS ;; c)%V) mi qi.
Proof.
move=>IH. elim: r; intros.
rewrite big_nil; apply: equal_OS_DS_skip.
rewrite big_cons; apply: equal_OS_DS_seqc=>//.
move=>m q; apply: equal_OS_DS_seqc=>//.
apply: equal_OS_DS_assign.
Qed.

Lemma summable_norm_sumE {I : choiceType} {R : realType} {C : extNumType R}
  {V : normedModType C} (f : {summable I -> V}) : `|f| = sum \`| f |.
Proof. by rewrite/Num.Def.normr/=/summable_norm/sum. Qed.

Lemma equal_OS_DS_abort (mi : cmem) (qi : 'End(Hq)) : ind_hyp abort_ mi qi.
Proof.
split=>??; first by rewrite/psum big1// =>i _; rewrite/opfun/=; case: (fsval i); rewrite/= normr0.
by rewrite/= abort_semE soE /opsum (fin_supp_sum (S := fset0)) ?psum0//=; case.
Qed.

Lemma equal_OS_DS_if e c1 c2 :
  (forall (mi : cmem) (qi : 'End(Hq)), ind_hyp c1 mi qi) ->
  (forall (mi : cmem) (qi : 'End(Hq)), ind_hyp c2 mi qi) ->
  forall (mi : cmem) (qi : 'End(Hq)), ind_hyp (cond_ e c1 c2)%V mi qi.
Proof.
move=>IHc1 IHc2 mi qi.
case E: (esem e mi); rewrite/opsum.
  pose h := (fun r => TR_cond1 r).
  pose h' := (fun r => match r with | TR_cond1 r => Some r | _ => None end).
  pose hx := opfun c1 mi qi.
  split=>[Pq S|mo Pq].
    rewrite (@psum_Sj _ _ h h' _ _ (TR_skip))/opfun//=. by case.
    by case=>// r/=; rewrite ?E/= normr0.
    by rewrite E; apply: (proj1 (IHc1 mi qi) Pq).
  have shx : summable hx by exists `|qi|; near=>J; apply: (proj1 (IHc1 mi qi) Pq).
  have Ph : ((fun r : trans_route => match eval_route r (cond_ e c1 c2)%V (mi, qi) with
                                    | Some t => sunit_def t.1 t.2 : {summable _ -> _}
                                    | None => 0
                                    end) \o h)%FUN = hx.
    by apply/funext=>r/=; rewrite E.
  rewrite/opsum (@sum_reindex _ _ _ _ _ h h')=>[//||||]; first by case.
  by case=>// r/=; rewrite/opfun/= E/=.
  by rewrite Ph.
  by rewrite Ph/hx/= E; apply (proj2 (IHc1 mi qi) mo Pq).
pose h := (fun r => TR_cond2 r).
pose h' := (fun r => match r with | TR_cond2 r => Some r | _ => None end).
pose hx := opfun c2 mi qi.
split=>[Pq S|mo Pq].
  rewrite (@psum_Sj _ _ h h' _ _ (TR_skip))/opfun//=. by case.
  by case=>// r/=; rewrite ?E/= normr0.
  by rewrite E; apply: (proj1 (IHc2 mi qi) Pq).
have shx : summable hx by exists `|qi|; near=>J; apply: (proj1 (IHc2 mi qi) Pq).
have Ph : ((fun r : trans_route => match eval_route r (cond_ e c1 c2)%V (mi, qi) with
                                    | Some t => sunit_def t.1 t.2 : {summable _ -> _}
                                    | None => 0
                                    end) \o h)%FUN = hx.
  by apply/funext=>r/=; rewrite E.
rewrite/opsum (@sum_reindex _ _ _ _ _ h h')=>[//||||]; first by case.
by case=>// r/=; rewrite/opfun/= E/=.
by rewrite Ph.
by rewrite Ph/hx/= E; apply (proj2 (IHc2 mi qi) mo Pq).
Unshelve. all: end_near.
Qed.

Fixpoint route_W_size r :=
  match r with
  | TR_while1 (TR_seqc r1 r2) => (route_W_size r2).+1
  | _ => 0%N
  end.

Fixpoint route_WC_size r :=
  match r with
  | TR_while1 (TR_seqc r1 r2) => (route_WC_size r2).+1
  | TR_cond1 (TR_seqc r1 r2) => (route_WC_size r2).+1
  | _ => 0%N
  end.

Lemma route_WC_size_ind (P : trans_route -> Prop) :
  (forall n, (forall r, (route_WC_size r < n)%N -> P r) -> 
    forall r, route_WC_size r = n -> P r) -> forall r, P r.
Proof.
move=>IH r.
have [n Pn]: exists n, route_WC_size r = n 
  by exists (route_WC_size r).
by elim/ltn_ind: n r Pn=>n Pn; apply/IH=>r Pr; apply/(Pn _ Pr).
Qed.

Fixpoint route_W2C r : trans_route :=
  match r with
  | TR_while1 (TR_seqc r1 r2) => TR_cond1 (TR_seqc r1 (route_W2C r2))
  | TR_while0 => TR_cond2 TR_skip
  | TR_cond1 (TR_seqc r1 r2) => TR_while1 (TR_seqc r1 (route_W2C r2))
  | TR_cond2 TR_skip => TR_while0
  | _ => r
  end.

Lemma route_W2CK : cancel route_W2C route_W2C.
Proof.
elim/route_WC_size_ind=>n IH.
by case=>//; case=>//= r1 r2 P; do ! f_equal; apply: IH; rewrite -P.
Qed.

Fixpoint while_syn_iter e c n :=
  match n with
  | 0%N => abort_
  | S n => cond_ e (c ;; while_syn_iter e c n)%V skip_
  end.

Lemma eval_route_WE e c r n :
  (route_W_size r < n)%N -> forall mi qi, 
    eval_route r (while_ e c) (mi,qi) = eval_route (route_W2C r) (while_syn_iter e c n) (mi,qi).
Proof.
elim: n r=>//= n IH.
case=>//=; case=>//=; intros; case: (esem e mi)=>//.
by case: (eval_route r1 c (mi, qi))=>//[[a1 a2]]; apply/IH/H.
Qed.

Lemma eval_route_WEN e c r n :
  (route_W_size r >= n)%N -> forall mi qi, 
    eval_route (route_W2C r) (while_syn_iter e c n) (mi,qi) = None.
Proof.
elim: n r=>//=[r _ mi qi|n IH r Pr mi qi].
case: (route_W2C r)=>//.
case: r Pr=>//=; case=>//= r1 r2; rewrite ltnS=>Pn.
case: (esem e mi)=>//; case: (eval_route r1 c (mi, qi))=>//[[a1 a2]].
by rewrite IH.
Qed.

Lemma equal_OS_DS_while_syn_iter e c:
  (forall (mi : cmem) (qi : 'End(Hq)), ind_hyp c mi qi) ->
  forall n mi qi, ind_hyp (while_syn_iter e c n) mi qi.
Proof.
move=>Hc; elim=>/=.
apply: equal_OS_DS_abort.
move=>n IH; apply: equal_OS_DS_if.
by apply: equal_OS_DS_seqc.
apply: equal_OS_DS_skip.
Qed.

Lemma equal_OS_DS_while_sem_iter e c:
  (forall (mi : cmem) (qi : 'End(Hq)), ind_hyp c mi qi) ->
  forall n mi qi mo, 0%:VF ⊑ qi ->
  opsum (while_syn_iter e c n) mi qi mo = 
  while_sem_iter e (sem_aux c) n mi mo qi.
Proof.
move=>Hc n mi qi mo Pq.
rewrite (proj2 (equal_OS_DS_while_syn_iter e Hc n mi qi) mo Pq).
do ! f_equal; by elim: n=>//= n->.
Qed.

Lemma equal_OS_DS_while e c :
  (forall (mi : cmem) (qi : 'End(Hq)), ind_hyp c mi qi) ->
  forall (mi : cmem) (qi : 'End(Hq)), ind_hyp (while_ e c) mi qi.
Proof.
move=>IH.
have P0: forall mi qi,  opfun_summable (while_ e c) mi qi.
  move=>mi qi Pq S; rewrite/opfun.
  pose n := (\max_(i <- (route_W_size @` S)%fset) i).+1.
  apply/(le_trans _ (proj1 (equal_OS_DS_while_syn_iter e IH n mi qi) Pq (route_W2C @` S)%fset)).
  rewrite [X in _ <= X]psum_seq_fsetE big_imfset=>[?? _ _|]; first by apply/(can_inj route_W2CK).
  rewrite-psum_seq_fsetE; apply/ler_sum=>i _.
  suff >/(eval_route_WE e c)/(_ mi qi)->: (route_W_size (val i) < n)%N by [].
  have Phi: route_W_size (val i) \in (route_W_size  @` S)%fset.
  by apply/imfsetP; exists (val i)=>//; case: i.
  by rewrite/n ltnS big_seq_fsetE/= (bigmax_sup [`Phi]%fset)//.
move=>mi qi; split=>// mo Pq.
rewrite /opsum sum_summableE.
  by apply/norm_bounded_cvg; exists `|qi|; near=>J; apply: P0.
rewrite -(summable_sigma_nat_lim route_W_size).
  exists `|qi|. near=>J. apply: (le_trans _ (P0 mi qi Pq J)).
  apply/ler_sum=>i _; 
  by move: (psum_norm_ler_norm (opfun (while_ e c) mi qi (val i)) [fset mo]%fset); rewrite psum1.
rewrite -while_sem_limEEE -/sem_aux.
apply: eq_lim=>n.
rewrite -equal_OS_DS_while_sem_iter//.
rewrite/opsum sum_summableE.
  apply/norm_bounded_cvg; exists `|qi|; near=>J.
  apply: (proj1 (equal_OS_DS_while_syn_iter e IH n mi qi) Pq J).
pose h := (fun i => route_W2C (val i)) 
  : {i : trans_route | (route_W_size i < n)%N} -> trans_route.
pose h' := (fun i => match asboolP (route_W_size (route_W2C i) < n)%N with
  | ReflectT Q => Some (exist (fun j => (route_W_size j < n)%N) _ Q)
  | ReflectF _ => None end).
rewrite -(@sum_reindexV _ _ _ _ _ h h')=>[[i/=Pi]|i|/=i||].
- by rewrite/h/h'/= route_W2CK; case: asboolP=>// p; rewrite (eq_irrelevance Pi p).
- by rewrite/h/h'/=; case: asboolP=>//= p; rewrite route_W2CK.
- rewrite/h'; case: asboolP=>//=/negP+ _; rewrite -leqNgt/opfun;
  by move=>/(eval_route_WEN e c)/(_ mi qi); rewrite route_W2CK=>->; rewrite summableE.
- exists `|qi|; near=>J.
  apply/(le_trans _ (proj1 (equal_OS_DS_while_syn_iter e IH n mi qi) Pq J)).
  apply/ler_sum=>i _. 
  by move: (psum_norm_ler_norm (opfun (while_syn_iter e c n) mi qi (val i)) [fset mo]%fset); rewrite psum1.
- apply: eq_sum=>[[i Pi]].
- by rewrite/opfun (eval_route_WE _ _ Pi)/=/h/=.
Unshelve. all: end_near.
Qed.

Lemma equal_OS_DS (c : cmd_) (mi : cmem) (qi : 'End(Hq)) :
  ind_hyp c mi qi.
Proof.
move: mi qi. dependent induction c.
- apply: equal_OS_DS_abort.
- apply: equal_OS_DS_skip.
- apply: equal_OS_DS_assign.
- intros.
  pose h := (fun v : (eval_ctype t) => TR_random v).
  pose h' := (fun r => match r with
              | TR_random t' v => match asboolP (t' = t) with
                                  | ReflectT Q => let: erefl in _ = t := Q return option (eval_ctype t) in Some v
                                  | _ => None
                                  end
              | _ => None
              end).
  have ph : pcancel h h' by move=>v/=; case: asboolP=>// p; rewrite eq_axiomK.
  have oh : ocancel h' h by case=>// t' v/=; case: asboolP=>//= p; 
    move: p {+}p=>/esym p; case: t' / p v=>v p; rewrite eq_axiomK.
  split=>[Pq S|mo _].
    rewrite (@psum_Sj _ _ _ _ ph oh (witness (eval_ctype t)))/opfun/=.
    move=>r Pr; apply/normr0P/eqP; case: r Pr=>// t' v/=; case: asboolP=>//= p. 
    by move: p {+}p=>/esym p; case: t' / p v=>v p; rewrite eq_axiomK.
    case: asboolP=>// p; rewrite eq_axiomK/=/psum.
    under eq_bigr do rewrite sunit_normE normrZ (ger0_norm (ge0_mu _ _)).
    by rewrite -mulr_suml ler_piMl// psum_le1_mu.
  pose hx := (fun v => sunit_def (mi.[c <- v])%M ((esem e mi v) *: qi) : {summable _ -> _}).
  have shx : summable hx.
    exists `|qi|; near=>J.
    apply/(le_trans (y := psum (fun x => (esem e mi x) * `|qi|) J)).
    apply: ler_sum=>i _; rewrite/hx/=/normf summable_norm_sumE (fin_supp_sum (S := [fset (mi.[c <- fsval i])%M])).
    by move=>j; rewrite inE/==>/negPf; rewrite /sunit_def=>->; rewrite normr0.
    by rewrite psum1/= /sunit_def eqxx normrZ ger0_norm// ge0_mu.
    by rewrite/psum -mulr_suml ler_piMl// psum_le1_mu.
  have Ph: ((fun r : trans_route => match eval_route r (c <$- e)%V (mi, qi) with
    | Some t0 => sunit_def t0.1 t0.2 : {summable _ -> _}
    | None => 0
    end) \o h)%FUN = hx.
    by apply/funext=>v; rewrite/=; case: asboolP=>[p|//]; rewrite eq_axiomK/=.
  rewrite/opsum (sum_reindex ph oh)/opfun.
  by case=>// t' v/=; case: asboolP=>//= p; 
    move: p {+}p=>/esym p; case: t' / p v=>v p; rewrite eq_axiomK.
  by rewrite Ph.
  rewrite Ph/hx/=/sdlet_def sum_summable_soE.
    apply: norm_bounded_cvg. exists `|\:1 : 'SO(Hq)|.
    near=>J. apply/(le_trans (y := psum (fun x => (esem e mi x) * `|\:1 : 'SO(Hq)|) J)).
    apply: ler_sum=>i _; rewrite /sunit_def /normf; case: eqP=>_.
    by rewrite/=/sdistr_def normrZ ger0_norm// ge0_mu.
    by rewrite normr0 mulr_ge0// ge0_mu.
    by rewrite /psum -mulr_suml ler_piMl// psum_le1_mu.
  rewrite sum_summableE; first by move: (summable_cvg (f := Summable.build shx)).
  f_equal; apply/funext=>r; rewrite/=/sunit_def.
  by case: eqP=>?; rewrite /sdistr_def !soE.
- by apply: equal_OS_DS_if.
- by apply: equal_OS_DS_while.
- intros.
  pose h := (fun r => TR_for r).
  pose h' := (fun r => match r with | TR_for r => Some r | _ => None end).
  pose hx := opfun (\big[seqc_/skip_]_(i <- esem e mi) (seqc_ (assign_ c i%:CS) c0)) mi qi.
  split=>[Pq S|mo Pq].
    rewrite (@psum_Sj _ _ h h' _ _ (TR_skip))/opfun//=. by case.
    by case=>// r/=; rewrite ?E/= normr0.
    by apply: (proj1 (equal_OS_DS_big c (esem e mi) IHc mi qi) Pq).
  have shx : summable hx.
    exists `|qi|; near=>J.
    by apply: (proj1 (equal_OS_DS_big c (esem e mi) IHc mi qi) Pq J). 
  have Ph : ((fun r : trans_route => match eval_route r (for_ c e c0)%V (mi, qi) with
      | Some t0 => sunit_def t0.1 t0.2  : {summable _ -> _}
      | None => 0
      end) \o h)%FUN = hx.
    by apply/funext=>r/=.
  rewrite/opsum (@sum_reindex _ _ _ _ _ h h')=>[//||||].
  1,2: by case.
  by rewrite Ph.
  by rewrite Ph/=/hx (proj2 (equal_OS_DS_big c (esem e mi) IHc mi qi) mo Pq) sem_aux_big.
- by apply: equal_OS_DS_seqc.
- split=>[Pq S|mo _].
    apply/(le_trans (y := psum \`| opfun (initial_ q e) mi qi | [fset TR_initial]%fset)).
    by apply: psum_lerG=>// i; rewrite !inE/opfun/==>/andP[]+ _; case: i=>//=; rewrite ?eqxx ?normr0.
    by rewrite psum1/opfun/= sunit_normE !psd_trfnorm ?qo_trlfE ?cp_psdP ?psdlfE ?Pq.
  rewrite/= /opsum (fin_supp_sum (S := [fset TR_initial])) ?psum1//=.
  by case; rewrite ?inE// eqxx. by rewrite /sunit_def; case: eqP; rewrite// soE.
- split=>[Pq S|mo _].
    apply/(le_trans (y := psum \`| opfun (unitary_ q e) mi qi | [fset TR_unitary]%fset)).
    by apply: psum_lerG=>// i; rewrite !inE/opfun/==>/andP[]+ _; case: i=>//=; rewrite ?eqxx ?normr0.
    by rewrite psum1/opfun/= sunit_normE !psd_trfnorm ?qo_trlfE ?cp_psdP ?psdlfE ?Pq.
  rewrite/= /opsum (fin_supp_sum (S := [fset TR_unitary])) ?psum1//=.
  by case; rewrite ?inE// eqxx. by rewrite /sunit_def; case: eqP; rewrite// soE.
- have M_inj t (x y : eval_qtype t) : TR_measure x = TR_measure y -> x = y.
    by move=>He; inversion He as [H1]; apply/(inj_existT H1).
  split=>[Pq S|mo _].
    apply/(le_trans (y := psum \`| opfun (measure_ c q e) mi qi | (TR_measure @` (@fsetT (eval_qtype tc))))).
    apply: psum_lerG=>// i; rewrite !inE/opfun/==>/andP[]+ _; case: i=>//=; rewrite ?eqxx ?normr0//.
    move=>tc'; case: asboolP=>[p|]; last by rewrite normr0.
    case: tc / p c e=>c e v /negP P; exfalso; apply: P; apply/imfsetP; exists v=>//; apply: in_fsetT.
    rewrite psum_seq_fsetE big_imfset//= =>[x y _ _ /M_inj//|].
    rewrite -big_seq_fsetT/opfun/=; case: asboolP=>//?; rewrite eq_axiomK/=.
    move: {+}Pq; rewrite -psdlfE=>Pq'; rewrite psd_trfnorm//.
    under eq_bigr do rewrite sunit_normE (psd_trfnorm (cp_psdP _ Pq'))/= liftfso_elemso.
    under eq_bigr do rewrite soE; by apply tn_trlf_psd.
  rewrite/= /opsum/opfun (fin_supp_sum (S := TR_measure @` (@fsetT (eval_qtype tc))))/=.
  case=>// tc' v/=; case: asboolP=>// Ptc /negP HC; exfalso; apply: HC.
  by move: Ptc=>/esym Ptc; case: tc' / Ptc v=> v; apply/imfsetP; exists v=>//; exact: in_fsetT.
  rewrite psum_seq_fsetE big_imfset//= =>[x y _ _ /M_inj//|].
  case: asboolP=>//?; rewrite eq_axiomK/=.
  rewrite/sdlet_def (fin_supp_sum (S := fsetT))=>[i|]; first by rewrite in_fsetT.
  rewrite psum_seq_fsetE summable_sumE soE; apply eq_bigr=>i _.
  by rewrite/= /sunit_def; case: eqP=>[_|]; rewrite ?liftfso_elemso// soE.
Unshelve. all: end_near.
Qed.

End Operational_Semantics.

Section Example.
Require Import qtype.
Local Open Scope vsyn_scope.
Local Open Scope xsyn_scope.
Local Open Scope nat_scope.
Local Open Scope string_scope.

Section Shor.

Definition extendedGCD (a' b' : expr_ nat) (fractions : cvar (CSeq CNat)) 
  (l := "extendedGCD")
  (a := CVar CNat l "a")
  (b := CVar CNat l "b")
  (tA := CVar CNat l "tA") := 
  a <<- a';;
  b <<- b';;
  fractions <<- [::]%:CS ;;
  While (b != 0%:CS) Do {
    fractions <<- (a %/ b) :: fractions;;
    tA <<- a %% b;;
    a <<- b;;
    b <<- tA
  }.

(* reasoning about quantum programs with classical variables. *)

Definition gcd (a' b' : expr_ nat) (res : cvar CNat)
  (l := "gcd")
  (a := CVar CNat l "a") (* a : gcd.a *)
  (b := CVar CNat l "b")
  (tA := CVar CNat l "tA") :=
  a <<- a';;
  b <<- b';;
  While (b != 0%:CS) Do {
    tA <<- a %% b;;
    a <<- b;;
    b <<- tA
  };;
  res <<- a
  .

Definition partial (fractions' : expr_ (seq nat)) (depth' : expr_ nat) (c : cvar CNat)
  (l := "partial")
  (r := CVar CNat l "r")
  (i := CVar CNat l "i")
  (tR := CVar CNat l "tR") :=
  c <<- 0%:CS;;
  r <<- 1%:CS;;
  For i in (index_iota%:F2 (0%:CS) depth') Do {
    tR <<- fractions' .[(size%:F1 fractions') -n depth' +n i] *n r +n c;;
    c <<- r;;
    r <<- tR
  }.

Definition cf (y' Q' N' : expr_ nat) (r : cvar CNat)
  (l := "cf")
  (fractions := CVar (CSeq CNat) l "fractions")
  (d := CVar CNat l "d")
  (tR := CVar CNat l "tR")
  (b := CVar (QType QBool) l "b") :=
  extendedGCD y' Q' fractions;;
  r <<- 0%:CS;;
  b <<- true%:CS ;;
  For d in (index_iota%:F2 (2%N%:CS) ((size%:F1 fractions) +n 1%:CS) ) Do {
    IfT b then {
      partial fractions d tR;;
      IfT (tR == r) || (N' <= tR) then
        b <<- false%:CS;;
      IfT b then
        r <<- tR
    }
  }.

Definition modExp (a' exp' mod' : expr_ nat) (fx : cvar CNat) 
  (l := "modExp")
  (a := CVar CNat l "a")
  (exp := CVar CNat l "exp") :=
  a <<- a' ;;
  exp <<- exp' ;;
  fx <<- 1%:CS ;;
  While (0%:CS < exp) Do {
    IfT (exp %% 2%:CS == 1%:CS) then
      fx <<- (fx *n a) %% mod' ;;
    a <<- (a *n a) %% mod' ;;
    exp <<- exp %/ 2%:CS
  }.

End Shor.

End Example.
