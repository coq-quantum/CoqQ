From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.classical Require Import boolp classical_sets.
From mathcomp.analysis Require Import -(notations)forms.
From mathcomp.analysis Require Import reals topology normedtype.
From quantum.external Require Import complex.
(* From mathcomp.real_closed Require Import complex. *)
Require Import mcextra mcaextra notation quantum
  orthomodular hspace inhabited autonat.

(* memory model *)
(* From mathcomp.real_closed Require Import complex. *)
From quantum Require Import hermitian prodvect tensor mxpred
  cpo extnum ctopology.
Require Import Coq.Program.Equality String.
(* Require Import Relation_Definitions Setoid. *)

(****************************************************************************)
(*  Extra of hspace.v, formalizing infinite caps and cups of Hilbert        *)
(*  subspaces and related theories.                                         *)
(*  We first consider hspace as a set and use "forall" to define its        *)
(*  infinite meet. Then, based on the properties of hspace, the infinite    *)
(*  meet set actually satisfies Pclosed condition, thus an equivalent       *)
(*  hspace can be extracted. Finally, infinite join is defined by meet.     *)
(* ------------------------------------------------------------------------ *)
(* * Operations :                                                           *)
(*     \cups_ ( i in P ) F : infinite join of hspace (index from P)         *)
(*      \cups_ ( i : T ) F : infinite join of hspace (index from T)         *)
(*      \cups_ ( i < n ) F : infinite join of hspace (index from `I_n)      *)
(*     \caps_ ( i in P ) F : infinite meet of hspace (index from P)         *)
(*      \caps_ ( i : T ) F : infinite meet of hspace (index from T)         *)
(*      \caps_ ( i < n ) F : infinite meet of hspace (index from `I_n)      *)
(*                                                                          *)
(*          extract_hspace : extract subhspace from a Pclosed predicate     *)
(* ------------------------------------------------------------------------ *)
(* * Theories :                                                             *)
(*  In addition to the theories of finite join/meet, we implement various   *)
(*  lemmas about formh, supph, kerh.                                        *)
(*  extract_correct : rewrite from set to extract_hspace                    *)
(*  ohspace_correct : rewrite from infinite cups to finite cups             *)
(****************************************************************************)

Import Order.TTheory GRing.Theory Num.Theory Num.Def.
Import HermitianTopology.
Local Notation C := hermitian.C.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Reserved Notation "\cups_ ( i 'in' P ) F"
  (at level 41, F at level 41, i, P at level 50,
           format "'[' \cups_ ( i  'in'  P ) '/  '  F ']'").
Reserved Notation "\cups_ ( i : T ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \cups_ ( i  :  T ) '/  '  F ']'").
Reserved Notation "\cups_ ( i < n ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \cups_ ( i  <  n ) '/  '  F ']'").
Reserved Notation "\cups_ i F"
  (at level 41, F at level 41, i at level 0,
           format "'[' \cups_ i '/  '  F ']'").
Reserved Notation "\caps_ ( i 'in' P ) F"
  (at level 41, F at level 41, i, P at level 50,
           format "'[' \caps_ ( i  'in'  P ) '/  '  F ']'").
Reserved Notation "\caps_ ( i : T ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \caps_ ( i  :  T ) '/  '  F ']'").
Reserved Notation "\caps_ ( i < n ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \caps_ ( i  <  n ) '/  '  F ']'").
Reserved Notation "\caps_ i F"
  (at level 41, F at level 41, i at level 0,
           format "'[' \caps_ i '/  '  F ']'").
Notation "x '`=>`' y" := (sasaki_hook x y) (at level 70) : hspace_scope.
Notation "x '`&&`' y" := (sasaki_projection x y) (at level 70) : hspace_scope.

HB.lock
Definition formh U V (u : 'FI(U,V)) (h : {hspace U}) := HSType (formlf u h).

Lemma formh_comp U V W (f1 : 'FI(U,V)) (f2 : 'FI(W,U)) A :
  formh f1 (formh f2 A) = formh (f1 \o f2) A.
Proof.
rewrite formh.unlock; apply/eq_hs/lfunP.
by rewrite -formlf_comp/= hsE formlf_comp.
Qed.

Lemma hseqP U (A B : {hspace U}) :
  reflect (forall x, (x \in A) = (x \in B)) (A == B).
Proof.
apply /(iffP eqP) =>[->//|H].
apply /le_anti /andP; split; apply /lehP =>x; by rewrite H.
Qed.

Lemma psdf_dot_eq0P (U : chsType) (f: 'F+(U)) x :
  [< x; f x >] = 0 -> f x = 0.
Proof.
rewrite spectralE /spectral sumoutpE sum_lfunE linear_sum/==> P1.
rewrite big1// =>i _.
suff: [< x; (hspace.eigenval i *: [> hspace.eigenvec i; hspace.eigenvec i <]) x >] = 0.
rewrite lfunE dotpZr/= outpE=>/eqP; rewrite mulf_eq0=>/orP[].
by move=>/eqP->; rewrite scale0r.
by rewrite dotpZr -conj_dotp -normCKC expf_eq0/= normr_eq0=>/eqP->;
  rewrite conjC0 scale0r scaler0.
apply: (psumr_eq0P _ P1)=>//= j _; rewrite lfunE dotpZr mulr_ge0//.
apply/ltW/eigenval_psd.
by rewrite /= outpE dotpZr -conj_dotp -normCKC exprn_ge0.
Qed.

Lemma psdf_dot_eq0E U (f: 'F+(U)) x : [< x; f x >] == 0 = (f x == 0).
Proof.
by apply/eqb_iff;
split=>[/eqP/psdf_dot_eq0P->//|/eqP->]; rewrite linear0.
Qed.

Section formh_extra.
Local Open Scope hspace_scope.
Variable (U V : chsType).

Lemma formhE (u : 'FI(U,V)) (h : {hspace U}) :
  formh u h = formlf u h :> 'End(V).
Proof. by rewrite formh.unlock hsE. Qed.
Lemma memh_form (u : 'FGI(U,V)) (h : {hspace U}) (v : V) :
  (v \in formh u h) = (u^A v \in h).
Proof.
by rewrite !memhE formhE/= -(inj_eq (isof_inj (u := u^A)))
  formlf.unlock -!comp_lfunE !comp_lfunA isofE comp_lfun1l.
Qed.
Lemma memh_formV (u : 'FI(U,V)) (h : {hspace U}) (v : U) :
  (v \in h) = (u v \in formh u h).
Proof.
by rewrite !memhE formhE/= formlf.unlock 
  -comp_lfunE isofK lfunE/= (inj_eq isof_inj).
Qed.
Lemma formh0 (u : 'FI(U,V)) : formh u `0` = `0`.
Proof.
by apply/hspacelfP; rewrite formh.unlock
  !hsE/= !hsE formlf.unlock comp_lfun0r comp_lfun0l.
Qed.
Lemma formhO (u : 'FGI(U,V)) (h : {hspace U}) :
  formh u (~` h) = ~` (formh u h).
Proof.
by apply/eqP/hseqP=>x;
rewrite memh_form !memhOE !ocomplK formh.unlock !hsE/= 
formlf.unlock/= -(inj_eq (isof_inj (u := u))) !lfunE/= lfunE/= linear0.
Qed.
Lemma formh1 (u : 'FGI(U,V)) : formh u `1` = `1`.
Proof. by rewrite -ocompl0 formhO formh0 ocompl0. Qed.
Lemma formhI (u : 'FGI(U,V)) (h1 h2 : {hspace U}) :
  formh u (h1 `&` h2) = formh u h1 `&` formh u h2.
Proof. by apply/eqP/hseqP=>x; rewrite memh_form !memhI !memh_form. Qed.
Lemma formhU (u : 'FGI(U,V)) (h1 h2 : {hspace U}) :
  formh u (h1 `|` h2) = formh u h1 `|` formh u h2.
Proof. by apply/ocompl_inj; rewrite -formhO !ocomplU formhI !formhO. Qed.
Lemma formhJ (u : 'FGI(U,V)) (h1 h2 : {hspace U}) :
  formh u (h1 `&&` h2) = (formh u h1 `&&` formh u h2).
Proof. by rewrite /sasaki_projection formhI formhU formhO. Qed.
Lemma formhH (u : 'FGI(U,V)) (h1 h2 : {hspace U}) :
  formh u (h1 `=>` h2) = (formh u h1 `=>` formh u h2).
Proof. by rewrite /sasaki_hook formhU formhI formhO. Qed.

Lemma formh_le (u : 'FGI(U,V)) P Q :
  formh u P `<=` formh u Q = (P `<=` Q).
Proof.
apply/eqb_iff; split=>/lehP H; apply/lehP=>v.
by move: (H (u v)); rewrite -!memh_formV.
by rewrite !memh_form; apply: H.
Qed.

End formh_extra.


Section hspace_extra.
Local Open Scope hspace_scope.
Variable (U : chsType).

(* generalize to U V *)
Lemma supph0 : supph (0 : 'End(U)) = `0`.
Proof.
apply/eqhP=>x; rewrite memh0; apply/eqb_iff; split.
by move/memh_suppP=>[y]; rewrite adjf0 lfunE/==>->.
by move=>/eqP->; apply/memh_suppP; exists 0; rewrite adjf0 lfunE.
Qed.

Lemma supph1 : supph (\1 : 'End(U)) = `1`.
Proof.
by apply/eqhP=>x; rewrite memh1; apply/memh_suppP;
exists x; rewrite adjf1 lfunE.
Qed.

(* generalize to U V *)
Lemma kerh0 : kerh (0 : 'End(U)) = `1`.
Proof. by rewrite kerhE supph0 hsO0. Qed.

Lemma kerh1 : kerh (\1 : 'End(U)) = `0`.
Proof. by rewrite kerhE supph1 hsO1. Qed.

Lemma eigenvec_mem (Q : 'FH(U)) i : 
  @hspace.eigenvec _ Q i \in supph Q.
Proof.
apply/memhP; rewrite supph_eigenE sumoutpE sum_lfunE (bigD1 i)//= big1.
by move=>j /negPf nji; rewrite scale1r outpE ponb_dot nji scale0r.
by rewrite scale1r outpE ponb_dot eqxx scale1r addr0.
Qed.

Lemma heigen_mem (Q : {hspace U}) i : 
  @heigen _ Q i \in Q.
Proof. rewrite -{2}[Q]supph_id; exact: eigenvec_mem. Qed.

Lemma supph_le_trlf0P (A : 'End(U)) (Q : {hspace U}) : 
  supph A `<=` Q -> (\Tr (A \o ~` Q) = 0).
Proof.
rewrite -lehO -kerhE => P.
rewrite heigenE sumoutpE linear_sumr linear_sum/= big1// =>i _.
rewrite scale1r outp_compr.
move: P=>/lehP/(_ _ (heigen_mem i)); rewrite memh_kerE=>/eqP->.
by rewrite out0p linear0.
Qed.

Lemma supph_eigenU (A : 'FH(U)) : 
  supph A = \cup_i <[(@hspace.eigenvec _ A i)]>.
Proof.
apply/le_anti/andP; split; apply/lehP=>x.
  rewrite memhE supph_eigenE sumoutpE=>/eqP P; apply/memh_cupP=>/=.
  exists (fun i=> [> hspace.eigenvec i; hspace.eigenvec i <] x).
    by move=>i _; rewrite outpE memhZ// memh_line.
    by rewrite -{1}P sum_lfunE; apply eq_bigr=>i _; rewrite scale1r.
move=>/memh_cupP/=[f Pf] ->.
apply/memh_cupl=>i _; move: (Pf i is_true_true).
by apply/lehP; rewrite -memhE_line eigenvec_mem.
Qed.

Lemma supph_leP (A : 'FH(U)) (Q : {hspace U}) :
  (forall i, @hspace.eigenvec _ A i \in Q) -> supph A `<=` Q.
Proof.
move=>P; rewrite supph_eigenU; apply/cuphsP=>/=i _.
by rewrite -memhE_line.
Qed.

Lemma supph_trlf0_le (A : 'F+) (Q : {hspace U}) :
  (\Tr (A \o ~` Q) = 0) -> supph A `<=` Q.
Proof.
move=>P; apply/supph_leP=>i; move: P=>/eqP;
rewrite [in X in X -> _](spectralE A) /spectral
  sumoutpE linear_suml/= linear_sum/=.
under eq_bigr do rewrite linearZl linearZ/= outp_compl outp_trlf adj_dotEl.
rewrite psumr_eq0.
  move=>/=j _; rewrite mulr_ge0//. apply/ltW/eigenval_psd.
  apply/psdlfP/is_psdlf.
move=>/allP/(_ i)/=; rewrite mem_index_enum=>/(_ is_true_true).
by rewrite mulf_eq0 eigenval_eq0/==>/eqP/psdf_dot_eq0P/eqP; rewrite memhOE.
Qed.

Lemma supp_le_trlfE (A : 'F+) (Q : {hspace U}) :
  (\Tr (A \o ~` Q) == 0) = (supph A `<=` Q).
Proof.
by apply/eqb_iff;
split=>[/eqP/supph_trlf0_le|/supph_le_trlf0P/eqP].
Qed.

Lemma obslf_le_supph (A : 'FO(U)) :
  A%:VF <= supph A.
Proof.
rewrite supph_eigenE [X in X <= _](spectralE A) /spectral
  !sumoutpE lev_sum //= =>i _.
apply/lev_pscale2; last by [].
by apply/ltW/eigenval_psd.
by apply/psdf_ge0.
by move: (eigenval_obs i)=>/andP[].
Qed.

(* extract subspace from a addcolsed and zclosed predicate *)
Definition Pclosed (s : set U) :=
  0 \in s /\ 
    forall c : C, forall x y : U, x \in s -> y \in s -> c *: x + y \in s.

Lemma Pclosed0 (s : set U) (H : Pclosed s) : (s `\ 0 =set0)%classic -> 
  forall x : U, x \in s = (x \in (`0` : {hspace U})).
Proof.
move=>P x; rewrite memh0.
apply/eqb_iff; split; last first.
by move=>/eqP->; case: H.
case: H=> + _. rewrite !inE=>P0.
move: (setD1K P0)=><-.
rewrite P/==>[[->//|//]].
Qed.

Definition updim (s : set U) n := 
  exists P : {hspace U}, (\Dim P <= n)%N /\ forall x, x \in s -> x \in P.

Lemma updim_dimU (s : set U) : updim s (dim U).
Proof.
exists `1`; split; first by rewrite dimh1.
by move=>x _; rewrite memh1.
Qed.

Definition Pdiff (s : set U) (x : U) :=
  [set y | (y \in s) /\ [< y ; x >] = 0]%classic.
Definition Pjoin (s : set U) (x : U) :=
  [set y | exists z, (z \in s /\ exists c, y = c *: x + z)]%classic.

Lemma Pclosed_diff (s : set U) (x : U) :
  Pclosed s -> Pclosed (Pdiff s x).
Proof.
move=>[] Ps0 Ps; split.
by rewrite inE /Pdiff/= Ps0 dot0p.
move=>c x1 x2; rewrite !inE /Pdiff/==>[[P11 P12] [P21 P22]].
split. by apply/Ps.
by rewrite dotpPl P12 P22 mulr0 addr0.
Qed.

Lemma Pclosed_diff_eq (s : set U) (x : U) :
  x \in s -> Pclosed s -> Pjoin (Pdiff s x) x = s.
Proof.
move=>Px []Ps0 Ps; apply/eq_set=>y; apply/propeqP; split.
move=>[z]; rewrite inE/Pdiff/==>[[[Pz1 Pz2]][c ->]].
by rewrite -in_setE; apply/Ps.
rewrite -in_setE=>Py.
pose c := [< x ; y >] * (([<x ; x >]^-1)^*)%R.
exists ((-c) *: x + y); split; last first.
by exists c; rewrite addrA -scalerDl subrr scale0r add0r.
rewrite inE /Pdiff /=; split; first by apply/Ps.
rewrite /c dotpDl dotpZl rmorphN rmorphM conj_dotp mulNr -mulrA conjCK.
case E: (x == 0).
by move: E=>/eqP->; rewrite dotp0 !mul0r addr0 oppr0.
by rewrite mulVf ?mulr1 ?addNr// dotp_eq0 E.
Qed.

Lemma Pdiff_dim (s : set U) (x : U) n :
  x != 0 -> x \in s -> updim s n -> updim (Pdiff s x) n.-1.
Proof.
move=>P1 P2 [V [] P3 P4]; exists (V `\` <[x]>); split.
  rewrite -ltnS; apply: (leq_trans _ (leqSpred _)); move: (dimhID V <[x]>).
  have /eqP-> : V `&` <[ x ]> == <[x]> by rewrite eq_caphr -memhE_line P4.
  by rewrite dim_hline P1 add1n=>->.
move=>v; rewrite /Pdiff /= inE /==> [[P5 P6]].
by rewrite diffhE memhI P4//= ocomplI memhUr// memhOE ocomplK hlineE hsE 
  /supplf lfunE/= outpE -conj_dotp P6 conjC0 scale0r linear0.
Qed.

Fixpoint extract_hspace_rec (s : set U) n : {hspace U} :=
  match n with
  | O => `0`
  | S n => match asboolP (s `\ 0 =set0)%classic with 
           | ReflectT _ => `0`
           | ReflectF _ => let x := xget 0 (s `\ 0)%classic in
                          <[ x ]> `|` extract_hspace_rec (Pdiff s x) n
           end
  end.

Definition extract_hspace (s : set U) := extract_hspace_rec s (dim U).

Lemma extract_correct1 (s : set U) n : Pclosed s ->
  updim s n -> forall x, x \in s = (x \in extract_hspace_rec s n).
Proof.
elim: n s.
  move=>s [] Ps0 Ps [h [Ph]] P x /=.
  apply/eqb_iff; split. 
  by move: Ph=>+/P; rewrite leqn0 dimh_eq0=>/eqP->.
  by rewrite memh0=>/eqP->.
move=>n IH s Ps Ph /= x.
case: asboolP.
by move=>/(Pclosed0 Ps)/(_ x).
move=>/eqP/set0P => P1.
case: xgetP; last by rewrite forallNP.
move=>y _ /= [] + /eqP yneq0; rewrite -in_setE=>Py.
rewrite -{1}(Pclosed_diff_eq Py Ps).
move: (IH _ (Pclosed_diff y Ps) (Pdiff_dim yneq0 Py Ph))=>P2.
apply/eqb_iff; split.
rewrite inE /Pjoin/==>[[x1 [Px1] [c ->]]].
apply/memhU. apply/memhZ_line. by rewrite -P2.
move=>/memhUP [] x1 /hlineP[c ->] [] x2 + ->.
rewrite -P2=>Px2.
rewrite inE/Pjoin/=; exists x2; split=>//.
by exists c.
Qed.

Lemma extract_correct (s : set U) : Pclosed s ->
  forall x, x \in s = (x \in extract_hspace s).
Proof. by move=>/extract_correct1/(_ (updim_dimU s)). Qed.

Lemma caps_pclosed (T : Type) (P : set T) (F : T -> {hspace U}):
  Pclosed [set x : U | forall i, P i -> x \in F i]%classic.
Proof.
split; first (by rewrite inE /= =>??; apply /mem0h);
by move=> c ??; rewrite !inE /= => Hx Hy b Pb;
apply: (memhD (memhZ c (Hx _ Pb)) (Hy _ Pb)).
Qed.

(* TODO : move *)
Lemma memh_Oproj (P : {hspace U}) x : P ((~` P) x) = 0.
Proof. by rewrite -{1}[P]ocomplK memh_projO. Qed.

Lemma shookhE (P Q : {hspace U}) :
  (P `=>` Q) = kerh (P \o (~` Q) \o P).
Proof.
rewrite /sasaki_hook; apply/le_anti/andP; split.
  apply/lehP=>x /memhUP[x1 +] [x2] /memhIP[] + + ->.
  rewrite memhOE ocomplK memhE memhOE memh_kerE=>/eqP P1 /eqP P2 /eqP P3.
  by rewrite linearD/= !lfunE/= P1 linear0 P2 lfunE/= P3 linear0 addr0.
apply/lehP=>x; rewrite memh_kerE (cplmt_dec P x) addrC -hs2lfOE linearD/=.
rewrite !lfunE/= memh_Oproj linear0 add0r projf_idemE=>/eqP P1.
apply/memhU. apply/memh_proj.
apply/memhIP; split; first by apply/memh_proj.
by rewrite memh_dotOE -adj_dotEr hermf_adjE -comp_lfunE P1 dotp0.
Qed.

Lemma sprojhE (P Q : {hspace U}) :
  P `&&` Q = supph (P \o Q \o P).
Proof. by rewrite -{1}[Q]ocomplK -shookO shookhE !ocomplK. Qed.

End hspace_extra.

(* now we can define the infinite join and meet of hspace *)
HB.lock
Definition bigcaph (U : chsType) I (P : set I) (F : I -> {hspace U}) :=
  extract_hspace [set x : U | forall i, P i -> x \in F i].
HB.lock
Definition bigcuph (U : chsType) I (P : set I) (F : I -> {hspace U}) :=
  (~` @bigcaph U I P (fun i => ~` F i))%HS.

Notation "\cups_ ( i 'in' P ) F" :=
  (@bigcuph _ _ P%classic (fun i => F%HS)) : hspace_scope.
Notation "\cups_ ( i : T ) F" :=
  (\cups_(i in @setT T) F)%HS : hspace_scope.
Notation "\cups_ ( i < n ) F" :=
  (\cups_(i in `I_n) F)%HS : hspace_scope.
Notation "\cups_ i F" := (\cups_(i : _) F)%HS : hspace_scope.
Notation "\caps_ ( i 'in' P ) F" :=
  (@bigcaph _ _ P%classic (fun i => F)) : hspace_scope.
Notation "\caps_ ( i : T ) F" :=
  (\caps_(i in @setT T) F)%HS : hspace_scope.
Notation "\caps_ ( i < n ) F" :=
  (\caps_(i in `I_n) F)%HS : hspace_scope.
Notation "\caps_ i F" := (\caps_(i : _) F)%HS : hspace_scope.

Section CapsCups.
Variable (U : chsType).
Local Open Scope order_scope.
Local Open Scope hspace_scope.
Import ComplLatticeSyntax.

(* move *)
Lemma formso_sumE V (x : 'CP(U,V)) : x = \sum_i formso (krausop x i) :> 'SO.
Proof.
apply/superopP=>u; rewrite krausE/= soE.
by apply eq_bigr=>i _; rewrite formsoE.
Qed.

Lemma kerh_cp_supp (E : 'CP(U)) (f : 'F+(U)) :
  kerh (E (supph f)) = kerh (E f).
Proof.
apply/eqP/hseqP=>x; rewrite !memh_kerE -!psdf_dot_eq0E/=.
rewrite formso_sumE !soE !sum_lfunE !dotp_sumr !psumr_eq0/=.
1,2: move=>i _; apply/psdlfP/is_psdlf.
apply/eqb_iff; split=>/allP P; apply/allP=>i Pi; move: (P i Pi);
rewrite !formsoE !lfunE/= !lfunE/= -adj_dotEl psdf_dot_eq0E
 -adj_dotEl psdf_dot_eq0E/=.
by rewrite -{2}(suppvlf f) hsE [in X in _ -> X]lfunE/==>/eqP->;
  rewrite linear0.
by rewrite hsE /supplf lfunE/==>/eqP->; rewrite linear0.
Qed.

Lemma supph_cp_supp (E : 'CP(U)) (f : 'F+(U)) :
  supph (E (supph f)) = supph (E f).
Proof. by rewrite supphE kerh_cp_supp -supphE. Qed.

Lemma supphD (f1 f2 : 'F+(U)) :
  supph (f1%:VF + f2) = supph f1 `|` supph f2.
Proof.
apply /le_anti /andP; split;
rewrite -lehO (ocomplU (supph f1) (supph f2)) -!kerhE; apply /lehP =>x;
rewrite (memhI x (kerh f1) (kerh f2)) !memh_kerE;
first by rewrite lfunE /= =>/andP[]/eqP->; rewrite add0r.
rewrite -!psdf_dot_eq0E/= lfunE/= dotpDr paddr_eq0//; apply/psdlfP/is_psdlf.
Qed.

Lemma kerhD (f1 f2 : 'F+(U)) :
  kerh (f1%:VF + f2) = kerh f1 `&` kerh f2.
Proof. by rewrite !kerhE supphD ocomplU. Qed.

Lemma supph_lef (f g : 'F+(U)) :
  f%:VF <= g -> supph f `<=` supph g.
Proof.
rewrite -subv_ge0 -psdlfE =>Pf.
by rewrite -(subrK f%:VF g) (PsdLf_BuildE Pf) supphD lehUr.
Qed.

Lemma kerh_lef (f g : 'F+(U)) :
  f%:VF <= g -> kerh g `<=` kerh f.
Proof. by move=>/supph_lef; rewrite !supphE lehO. Qed.

Section bigtheory.
Variable (I : Type).
Implicit Types (A : {hspace U}) (i : I) (P : set I) (F G : I -> {hspace U}).

Lemma caps_extract P F x: 
  is_true (x \in \caps_(i in P) F i)
    = forall i, P i -> x \in F i.
Proof.
rewrite bigcaph.unlock -extract_correct ?inE //; exact: caps_pclosed.
Qed.

Lemma caps_inf i P F : P i -> \caps_(j in P) F j `<=` F i.
Proof.
by move=> Pi; apply /lehP =>a; rewrite caps_extract; apply.
Qed.

Lemma cups_sup i P F : P i -> F i `<=` \cups_(j in P) F j.
Proof.
by move=> Pi; rewrite -lehO; apply /lehP=> a;
rewrite bigcuph.unlock ocomplK caps_extract; apply.
Qed.

Lemma leh_caps_r P : {homo (fun x : I -> {hspace U} => \caps_(i in P) x i)
  : F G / (forall i, F i `<=` G i) >-> F `<=` G}.
Proof.
move=> p q H; apply /lehP=> a; rewrite !caps_extract => Hx x Px;
apply: lehP _ _ (H x) a (Hx x Px).
Qed.

Lemma leh_cups_r P : {homo (fun x : I -> {hspace U} => \cups_(i in P) x i)
  : F G / (forall i, F i `<=` G i) >-> F `<=` G}.
Proof.
by move=>F G FG; rewrite bigcuph.unlock lehO;
apply/leh_caps_r=>i; rewrite lehO.
Qed.

(* Lemma eqEsubset A B : (A = B) = (A `<=` B /\ B `<=` A).
Proof.
rewrite propeqE; split=> [->//|[AB BA]].
by apply /le_anti/andP.
Qed. *)

Lemma hseq_split (A B : {hspace U}) :
  (forall x, (x \in A) -> (x \in B)) -> (forall x, (x \in B) -> (x \in A))
-> (A = B).
Proof.
by move=> H1 H2; apply /le_anti/andP; split; apply /lehP.
Qed.

Lemma eq_capsr P F G : (forall i, P i -> F i = G i) ->
  \caps_(i in P) F i = \caps_(i in P) G i.
Proof.
move=> H; apply: hseq_split=> x;
rewrite !caps_extract => H0 i Pi.
by rewrite -(H i Pi) (H0 i Pi).
by rewrite (H i Pi) (H0 i Pi).
Qed.

Lemma eq_cupsr P F G : (forall i, P i -> F i = G i) ->
  \cups_(i in P) F i = \cups_(i in P) G i.
Proof.
move=> H; rewrite bigcuph.unlock; f_equal; apply: eq_capsr.
by move=> i Pi; f_equal; apply: H i Pi.
Qed.

Lemma capsO P F :
  ~` (\caps_(i in P) F i) = \cups_(i in P) ~` (F i).
Proof.
by rewrite bigcuph.unlock; f_equal;
apply eq_capsr =>i Pi; rewrite ocomplK.
Qed.

Lemma cupsO P F :
  ~` (\cups_(i in P) F i) = \caps_(i in P) ~` (F i).
Proof.
by rewrite bigcuph.unlock ocomplK.
Qed.

Lemma eq_cupsl P Q F : (P `<=>` Q)%classic ->
  \cups_(i in P) F i = \cups_(i in Q) F i.
Proof. by move=> /seteqP->. Qed.

Lemma eq_capsl P Q F : (P `<=>` Q)%classic ->
  \caps_(i in P) F i = \caps_(i in Q) F i.
Proof. by move=> /seteqP->. Qed.

Lemma eq_cups P Q F G : (P `<=>` Q)%classic -> (forall i, P i -> F i = G i) ->
  \cups_(i in P) F i = \cups_(i in Q) G i.
Proof. by move=> /eq_cupsl<- /eq_cupsr->. Qed.

Lemma eq_caps P Q F G : (P `<=>` Q)%classic -> (forall i, P i -> F i = G i) ->
  \caps_(i in P) F i = \caps_(i in Q) G i.
Proof. by move=> /eq_capsl<- /eq_capsr->. Qed.

Lemma capsI P F G : \caps_(i in P) (F i `&` G i) =
  (\caps_(i in P) F i) `&` (\caps_(i in P) G i).
Proof.
apply: hseq_split=> x; rewrite memhI !caps_extract.
move =>H; apply/andP; split; rewrite caps_extract =>i Pi.
exact: (proj1 (memhIP (H i Pi))).
exact: (proj2 (memhIP (H i Pi))).
move =>/andP; rewrite !caps_extract => [[HF HG] i Pi];
apply /memhIP; split;
[exact: HF i Pi| exact: HG i Pi].
Qed.

Lemma cupsU P F G : \cups_(i in P) (F i `|` G i) =
  (\cups_(i in P) F i) `|` (\cups_(i in P) G i).
Proof.
by rewrite bigcuph.unlock -ocomplI -capsI; f_equal;
apply: eq_capsr=> ??; rewrite ocomplU.
Qed.

Lemma caps_const P A : (P !=set0)%classic -> \caps_(_ in P) A = A.
Proof.
case=> j H; apply: hseq_split=> x;
rewrite caps_extract//; apply; exact: H.
Qed.

Lemma cups_const P A : (P !=set0)%classic -> \cups_(_ in P) A = A.
Proof. 
by move=> H; rewrite bigcuph.unlock caps_const ?ocomplK.
Qed.

Lemma capsIl P F A : (P !=set0)%classic ->
  \caps_(i in P) (F i `&` A) = \caps_(i in P) F i `&` A.
Proof. by move=> PN0; rewrite capsI caps_const. Qed.

Lemma capsIr P F A : (P !=set0)%classic ->
  \caps_(i in P) (A `&` F i) = A `&` \caps_(i in P) F i.
Proof. by move=> PN0; rewrite capsI caps_const. Qed.

Lemma cupsUl P F A : (P !=set0)%classic ->
  \cups_(i in P) (F i `|` A) = \cups_(i in P) F i `|` A.
Proof. by move=> PN0; rewrite cupsU cups_const. Qed.

Lemma cupsUr P F A : (P !=set0)%classic ->
  \cups_(i in P) (A `|` F i) = A `|` \cups_(i in P) F i.
Proof. by move=> PN0; rewrite cupsU cups_const. Qed.

Lemma cups_set0 F : \cups_(i in set0) F i = `0`.
Proof.
rewrite bigcuph.unlock -(ocomplK `0`); f_equal; apply /eqP /hseqP =>a.
suff: a \in \caps_(i in set0) ~` F i by rewrite hsO0 memh1.
by rewrite caps_extract.
Qed.

Lemma cups_set1 F i : \cups_(j in [set i]) F j = F i.
Proof.
rewrite bigcuph.unlock -[RHS]ocomplK; f_equal; apply: hseq_split=> x;
rewrite caps_extract /=; by [move-> | move=>??->].
Qed.

Lemma caps_set0 F : \caps_(i in set0) F i = `1`.
Proof.
by apply: hseq_split=> x; rewrite caps_extract memh1.
Qed.

Lemma caps_set1 F i : \caps_(j in [set i]) F j = F i.
Proof.
by apply: hseq_split=> x; rewrite caps_extract /=;
[move->|move=>??->].
Qed.

Lemma cups0 P F :
  (forall i, P i -> F i = `0`) -> \cups_(i in P) F i = `0`.
Proof.
move=> H; rewrite bigcuph.unlock -[RHS]ocomplK ocompl0; f_equal.
apply /hseq_split =>x; rewrite caps_extract memh1// => _ i Pi.
by rewrite (H i Pi) ocompl0 memh1.
Qed.

Lemma caps0 P F :
  (exists2 i, P i & F i = `0`) -> \caps_(i in P) F i = `0`.
Proof.
move=> [i Pi Fi]; apply: hseq_split=> x; rewrite caps_extract ?memh0;
last by move=> /eqP-> j Pj; apply mem0h.
by move=> H; rewrite -memh0 -Fi (H i Pi).
Qed.

Lemma caps1 P F :
  (forall i, P i -> F i = `1`) -> \caps_(i in P) F i = `1`.
Proof.
move=> H; apply/ocompl_inj; rewrite capsO ocompl1 cups0// => i Pi.
by rewrite (H i Pi) ocompl1.
Qed.

Lemma cupsT P F :
  (exists2 i, P i & F i = `1`) -> \cups_(i in P) F i = `1`.
Proof.
move=> [i Pi Fi]; rewrite bigcuph.unlock -ocompl0; f_equal.
by apply: caps0; exists i; rewrite // Fi ocompl1.
Qed.

Lemma caps1P P F :
  (\caps_(i in P) F i = `1`) <-> forall i, P i -> F i = `1`.
Proof.
split; last exact: caps1; move=> /eqP /hseqP => H i Pi.
apply: hseq_split=> x; first by rewrite memh1.
rewrite -(H x) caps_extract; by apply.
Qed.

Lemma cups0P P F :
  (\cups_(i in P) F i = `0`) <-> forall i, P i -> F i = `0`.
Proof.
rewrite bigcuph.unlock -ocompl1; split.
by move=>/ocompl_inj; rewrite caps1P=> H i Pi; rewrite -(H i Pi) ocomplK.
by move=> H; f_equal; apply hseq_split=> x;
rewrite caps_extract memh1// => _ i Pi; rewrite (H i Pi) ocomplK memh1.
Qed.

Lemma cups_nonempty P F :
  (\cups_(i in P) F i != `0`) <-> exists2 i, P i & F i != `0`.
Proof.
split=> H; [apply: contra_neqP _ H | apply: contraPneq _ H];
rewrite cups0P -forallPNP=> H i Pi.
by apply: contraPeq Logic.I; rewrite notB; apply: H i Pi.
by rewrite (H i Pi) eqxx.
Qed.

Lemma memhB_commute (A B : {hspace U}) :
  (A _C_ B)%O -> forall x, x \in A `|` B -> x - A x \in B.
Proof.
move=> Hc x.
have ->: A `|` B = A `|` (B `&` ~` A) by
  rewrite -commute_char6 in Hc; rewrite -(eqP Hc) joinC.
move=>/memhUP [u Au [v Bv ->]]; move: Bv Au =>/memhIP [];
rewrite (memhOE (~`A) v) ocomplK (memhE A) => Bv /eqP Av /eqP Au.
by rewrite linearD /= Au Av addr0 addrAC addrN add0r.
Qed.

Lemma hsU_capsr F P A :
  (forall i, (A _C_ F i)%O) ->
  A `|` \caps_(i in P) F i = \caps_(i in P) (A `|` F i).
Proof.
move=> Hc; apply: hseq_split=> x.
by move /memhUP=> [u Au [v]];
rewrite !caps_extract=> H Xuv i Pi; rewrite Xuv memhU ?(H i Pi).
rewrite caps_extract=> H; apply /memhUP; exists (A x);
first by rewrite memhE projf_idemE.
exists (x - A x); last by rewrite addrCA addrN addr0.
rewrite caps_extract=> i Pi;
exact: (memhB_commute (Hc i) (H i Pi)).
Qed.

Lemma hsI_cupsr F P A :
  (forall i, (A _C_ F i)%O) ->
  A `&` \cups_(i in P) F i = \cups_(i in P) (A `&` F i).
Proof.
move=> Hc. rewrite bigcuph.unlock -{1}(ocomplK A) -ocomplU hsU_capsr;
first by move=> i; rewrite commuteOO Hc.
by under eq_capsr do rewrite -ocomplI.
Qed.

Lemma hsI_cupsl F P A :
  (forall i, (A _C_ F i)%O) ->
  \cups_(i in P) F i `&` A = \cups_(i in P) (F i `&` A).
Proof.
by move=> Hc; rewrite meetC hsI_cupsr//;
under eq_cupsr do rewrite meetC.
Qed.

Lemma hsU_capsl F P A :
  (forall i, (A _C_ F i)%O) ->
  \caps_(i in P) F i `|` A = \caps_(i in P) (F i `|` A).
Proof.
by move=> Hc; rewrite joinC hsU_capsr//;
under eq_capsr do rewrite joinC.
Qed.

Lemma cups_mkcond P F :
  \cups_(i in P) F i = \cups_i if i \in P then F i else `0`.
Proof.
rewrite bigcuph.unlock; f_equal; apply: hseq_split=> x;
rewrite !caps_extract=>/= H i Pi.
by case HPi: (i \in P); last (by rewrite ocompl0 memh1);
  apply: (H i); rewrite -inE HPi.
by move: (H i Logic.I); rewrite ifT ?inE.
Qed.

Lemma cups_mkcondr P Q F :
  \cups_(i in P `&` Q) F i = \cups_(i in P) if i \in Q then F i else `0`.
Proof.
rewrite cups_mkcond [RHS]cups_mkcond; apply: eq_cupsr => i _.
by rewrite in_setI; case: (i \in P) (i \in Q) => [] [].
Qed.

Lemma cups_mkcondl P Q F :
  \cups_(i in P `&` Q) F i = \cups_(i in Q) if i \in P then F i else `0`.
Proof.
rewrite cups_mkcond [RHS]cups_mkcond; apply: eq_cupsr => i _.
by rewrite in_setI; case: (i \in P) (i \in Q) => [] [].
Qed.

Lemma caps_mkcond F P :
  \caps_(i in P) F i = \caps_i if i \in P then F i else `1`.
Proof.
apply: ocompl_inj; rewrite !capsO cups_mkcond; apply: eq_cupsr => i _.
by case: ifP; rewrite ?hsO1.
Qed.

Lemma caps_mkcondr P Q F :
  \caps_(i in P `&` Q) F i = \caps_(i in P) if i \in Q then F i else `1`.
Proof.
rewrite caps_mkcond [RHS]caps_mkcond; apply: eq_capsr => i _.
by rewrite in_setI; case: (i \in P) (i \in Q) => [] [].
Qed.

Lemma caps_mkcondl P Q F :
  \caps_(i in P `&` Q) F i = \caps_(i in Q) if i \in P then F i else `1`.
Proof.
rewrite caps_mkcond [RHS]caps_mkcond; apply: eq_capsr => i _.
by rewrite in_setI; case: (i \in P) (i \in Q) => [] [].
Qed.

Lemma cups_setU F (X Y : set I) :
  \cups_(i in X `|` Y) F i = \cups_(i in X) F i `|` \cups_(i in Y) F i.
Proof.
rewrite bigcuph.unlock -ocomplI; f_equal; apply: hseq_split=> x.
rewrite caps_extract/= => H; apply /memhIP; split; rewrite caps_extract=> i Pi;
[exact: H i (or_introl Pi) | exact: H i (or_intror Pi)].
move /memhIP; rewrite !caps_extract /= => [[HX HY]] i [Xi|Yi];
[exact: HX | exact: HY].
Qed.

Lemma caps_setU F (X Y : set I) :
  \caps_(i in X `|` Y) F i = \caps_(i in X) F i `&` \caps_(i in Y) F i.
Proof. by apply: ocompl_inj; rewrite !(ocomplI, capsO) cups_setU. Qed.

Lemma cups_setU1 F (x : I) (X : set I) :
  \cups_(i in x |` X) F i = F x `|` \cups_(i in X) F i.
Proof. by rewrite cups_setU cups_set1. Qed.

Lemma caps_setU1 F (x : I) (X : set I) :
  \caps_(i in x |` X) F i = F x `&` \caps_(i in X) F i.
Proof. by rewrite caps_setU caps_set1. Qed.

Lemma cups_setD1 (x : I) F (X : set I) : X x ->
  \cups_(i in X) F i = F x `|` \cups_(i in X `\ x) F i.
Proof. by move=> Xx; rewrite -cups_setU1 setD1K. Qed.

Lemma caps_setD1 (x : I) F (X : set I) : X x ->
  \caps_(i in X) F i = F x `&` \caps_(i in X `\ x) F i.
Proof. by move=> Xx; rewrite -caps_setU1 setD1K. Qed.

(* Lemma cupsDr F (P : set I) A : (P !=set0)%classic ->
  \caps_(i in P) (A `\` F i) = A `\` \cups_(i in P) F i. *)

(* Lemma setD_cupsl F (P : set I) A :
  \cups_(i in P) F i `\` A = \cups_(i in P) (F i `\` A). *)

Lemma caps_setM_dep {J : Type} (F : I -> J -> {hspace U})
    (P : set I) (Q : I -> set J) :
  \caps_(k in P `*`` Q) F k.1 k.2 = \caps_(i in P) \caps_(j in Q i) F i j.
Proof.
apply: hseq_split=> x; rewrite !bigcaph.unlock -!extract_correct ?inE /=;
try exact: caps_pclosed.
move=> H i Pi; rewrite -extract_correct ?inE /=; try (exact: caps_pclosed);
move=> j Qij; exact: H (i, j) (conj Pi Qij).
move=> H ij [Pi Qij]; move: (H ij.1 Pi); rewrite -extract_correct ?inE /=;
first exact: caps_pclosed; by apply.
Qed.

Lemma caps_setM {J : Type} (F : I -> J -> {hspace U}) (P : set I) (Q : set J) :
  \caps_(k in P `*` Q) F k.1 k.2 = \caps_(i in P) \caps_(j in Q) F i j.
Proof. exact: caps_setM_dep. Qed.

Lemma cups_setM_dep {J : Type} (F : I -> J -> {hspace U})
  (P : set I) (Q : I -> set J) :
\cups_(k in P `*`` Q) F k.1 k.2 = \cups_(i in P) \cups_(j in Q i) F i j.
Proof.
rewrite bigcuph.unlock; f_equal; under [RHS]eq_capsr do rewrite ocomplK.
exact: caps_setM_dep.
Qed.

Lemma cups_setM {J : Type} (F : I -> J -> {hspace U}) (P : set I) (Q : set J) :
  \cups_(k in P `*` Q) F k.1 k.2 = \cups_(i in P) \cups_(j in Q) F i j.
Proof. exact: cups_setM_dep. Qed.

Lemma cupsID (Q : set I) F (P : set I) :
  \cups_(i in P) F i =
    (\cups_(i in P `&` Q) F i) `|` (\cups_(i in P `&` ~` Q) F i).
Proof. by rewrite -cups_setU -setIUr setUv setIT. Qed.

Lemma capsID (Q : set I) F (P : set I) :
  \caps_(i in P) F i =
    (\caps_(i in P `&` Q) F i) `&` (\caps_(i in P `&` ~` Q) F i).
Proof. by rewrite -caps_setU -setIUr setUv setIT. Qed.

Lemma caps_lub P F A :
  (forall i, P i -> A `<=` F i) -> A `<=` \caps_(j in P) F j.
Proof.
move=> H; apply /lehP=> x; rewrite caps_extract=> Hx i Pi;
exact: lehP _ _ (H i Pi) x Hx.
Qed.

Lemma cups_glb P F A :
  (forall i, P i -> F i `<=` A) -> \cups_(j in P) F j `<=` A.
Proof.
rewrite bigcuph.unlock -{2}(ocomplK A) lehO=> H;
apply: caps_lub=> i Pi; rewrite lehO; exact: H i Pi.
Qed.

Lemma caps_image {aT} (P : set aT) (f : aT -> I) F :
  \caps_(x in f @` P) F x = \caps_(x in P) F (f x).
Proof.
apply: hseq_split=> x; rewrite !bigcaph.unlock -!extract_correct ?inE /=;
try exact: caps_pclosed.
by move=> H a Pa; apply: H; exists a.
by move=> H i [a Pa]<-; apply: H.
Qed.

Lemma cups_image {aT} (P : set aT) (f : aT -> I) F :
  \cups_(x in f @` P) F x = \cups_(x in P) F (f x).
Proof.
rewrite bigcuph.unlock; f_equal; exact: caps_image.
Qed.

Lemma shook_caps F P A : 
  (A `=>` \caps_(i in P) F i) = \caps_(i in P) (A `=>` F i).
Proof.
rewrite /sasaki_hook.
case H0: (P == set0); first by rewrite (eqP H0) !caps_set0 meetx1 joinOx.
rewrite -capsIr; first by apply /set0P; rewrite H0.
by rewrite hsU_capsr// => i; rewrite commuteOx commutexIl.
Qed.

Lemma sproj_cups F P A :
  (A `&&` \cups_(i in P) F i) = \cups_(i in P) (A `&&` F i).
Proof.
rewrite /sasaki_projection.
case H0: (P == set0); first by rewrite (eqP H0) !cups_set0 joinx0 meetxO.
rewrite -cupsUr; first by apply /set0P; rewrite H0.
by rewrite hsI_cupsr// => i; rewrite -commuteOx commutexUl.
Qed.

Lemma supphD_le (A B : 'End(U)) :
  supph (A + B) `<=` supph A `|` supph B.
Proof.
by rewrite -lehO ocomplU; apply/lehP=>x; 
  rewrite memhI !memh_suppOE lfunE/==>/andP[]/eqP->/eqP->; rewrite addr0.
Qed.

Lemma supph_sum_le (r : seq I) (P : pred I) (F : I -> 'End(U)) :
  supph (\sum_(i <- r | P i) F i) `<=` \cup_(i <- r | P i) supph (F i).
Proof.
elim/big_rec2: _ => [|i y1 y2 _ Py]/=; first by rewrite supph0.
by apply/(le_trans (supphD_le _ _))/leU2=>[|//]; apply/lexx.
Qed.

Lemma cuphs_supp_le (r : seq I) F (P : pred I) (E : 'CP(U)) :
  supph (E (\cup_(i <- r | P i) F i)) `<=` \cup_(i <- r | P i) supph (E (F i)).
Proof.
elim/big_rec2: _ => [|i y1 y2 _ Py]/=; first by rewrite hsE linear0 supph0.
rewrite {1}/Order.join /= /cuph /= supph_cp_supp /= linearD /= supphD /=;
apply: leU2 =>[|//]. rewrite lexx//.
Qed.

End bigtheory.

Section supph_cups.
Variable (I : eqType).
Implicit Types (F : I -> {hspace U}) (l : seq I) (i : I) (s P : set I).

Definition left_nonempty F s l :=
  ([set i | (~` (\cup_(j <- l) F j) `&&` F i != `0`)%HS /\ (i \in s)] !=set0)%classic.

Lemma left_nonemptyNP F s l :
  ~ left_nonempty F s l <-> \cups_(j in s) F j `<=` \cup_(j <- l) F j.
Proof.
split.
  rewrite /left_nonempty/= -forallNP/= => IH.
  apply/cups_glb=>i Si.
  move: (IH i); rewrite not_andP inE=>[[|//]].
  by rewrite eq_sproj0 lehO=>/negP; rewrite negbK.
move=>IH; rewrite -forallNP=>i /=.
rewrite eq_sproj0 lehO inE=>[[/negP P1 Si]].
apply/P1/(le_trans (cups_sup _ Si) IH).
Qed.

Fixpoint ohspace_rec (F : I -> {hspace U}) (s: set I) l n :=
  match n with
  | O => l
  | S n =>
    match asboolP (left_nonempty F s l) with
    | ReflectF _ => l
    | ReflectT H => ohspace_rec F s ((projT1 (cid H)) :: l) n
    end
  end.

Definition ohspace F s := ohspace_rec F s nil (dim U).

Lemma ohspace_rec_iterP (F : I -> {hspace U}) (s: set I) l n :
  ohspace_rec F s l n =
    match asboolP (left_nonempty F s l) with
    | ReflectF _ => l
    | ReflectT H =>
      match n with
      | O => l
      | S n => ohspace_rec F s (projT1 (cid H) :: l) n
      end
    end.
Proof.
by case: n; simpl; case: asboolP.
Qed.

Lemma ohspace_rec_iterN (F : I -> {hspace U}) (s: set I) l n :
  ~ left_nonempty F s (ohspace_rec F s l n) ->
    ohspace_rec F s l n.+1 = ohspace_rec F s l n.
Proof.
elim: n l; first by move=> l /=; case: asboolP.
move=> n IH l /=; case: asboolP=> Leftl Fullonxl; last by [].
case: asboolP.
move=> Leftxl; rewrite -[RHS](IH _ Fullonxl) /=;
case: asboolP=> Leftxl2; by rewrite ?(Prop_irrelevance Leftxl Leftxl2).
rewrite ohspace_rec_iterP; by case: asboolP.
Qed.

Lemma ohspace_recE (F : I -> {hspace U}) (s: set I) l n :
  ohspace_rec F s l n.+1 =
  match asboolP (left_nonempty F s l) with
  | ReflectF _ => l
  | ReflectT H => ohspace_rec F s (sval (cid H) :: l) n
  end.
Proof. by []. Qed.

Lemma asboolP_matchE T (P : Prop) (f : P -> T) (g : ~ P -> T) (H : P) :
  match asboolP P with
  | ReflectT H => f H
  | ReflectF H => g H
  end = f H.
Proof. by case: asboolP=>// p; rewrite (Prop_irrelevance H p). Qed.

Lemma ohspace_rec_cats F s l n : 
  exists s1 : seq I, ohspace_rec F s l n = s1 ++ l.
Proof.
elim: n l=>[l |n IH l]/=; first by exists nil; rewrite cat0s.
case: asboolP=>p; last by exists nil; rewrite cat0s.
move: (IH (sval (cid p) :: l))=>[s1->]; exists (rcons s1 (sval (cid p))).
by rewrite cat_rcons.
Qed.

Lemma ohspace_rec_iterE (F : I -> {hspace U}) (s: set I) l n :
  ohspace_rec F s l n.+1 =
    match asboolP (left_nonempty F s (ohspace_rec F s l n)) with
    | ReflectF _ => ohspace_rec F s l n
    | ReflectT H => (projT1 (cid H)) :: ohspace_rec F s l n
    end.
Proof.
elim: n l; first by [].
move=> n IH l.
case: asboolP=>p; last exact: ohspace_rec_iterN.
rewrite ohspace_recE [RHS]/=.
have H : (left_nonempty F s l).
  move: p. move: (ohspace_rec_cats F s l n.+1)=>[s1 ->].
  apply contraPP=>/left_nonemptyNP P1; apply/left_nonemptyNP.
  by rewrite big_cat/=; apply/(le_trans P1)/leUr.
rewrite (asboolP_matchE _ _ H) [X in _ = _ :: X](asboolP_matchE _ _ H) IH.
by case: asboolP; move: p=>/=; 
  rewrite (asboolP_matchE _ _ H)=>p p0//; rewrite (Prop_irrelevance p p0).
Qed.

Lemma ohspace_rec_correct_in F s l n i :
  i \in ohspace_rec F s l n -> i \in s \/ i \in l.
Proof.
elim: n l; first by move=> l /= ->; right.
move => /= n IH l; case: asboolP=> p; last by move->; right.
move => /IH [H|]; first by left.
rewrite inE; move /orP=> [/eqP H | H]; last by right.
by left; move: (projT2 (cid p)); rewrite/= -H=> [[]].
Qed.

Lemma ohspace_correct_in (F : I -> {hspace U}) s (i : I) :
  i \in ohspace F s -> i \in s.
Proof.
rewrite /ohspace.
move /ohspace_rec_correct_in.
by rewrite inE in_nil=> [[]].
Qed.

Lemma le_cupo_cups (F : I -> {hspace U}) (s: set I) l n :
  \cup_(i <- ohspace_rec F s l n) F i <=
    \cups_(j in s) F j `|` \cup_(j <- l) F j.
Proof.
elim: n l; first by move=> l; apply: lehUr.
move=> n IH l /=; case: asboolP=> p; last by rewrite lehUr.
apply: (le_trans (IH _)); rewrite leUh lehUl /= big_cons lehU2//;
move: (projT2 (cid p)) => /= [_].
rewrite inE; apply: cups_sup.
Qed.

Lemma ohspace_rec_dim F s l (H : left_nonempty F s l) :
  (\Dim (\cup_(j <- l) F j) < \Dim (\cup_(j <- projT1 (cid H) :: l) F j))%N.
Proof.
rewrite (ltn_leqif (dimh_leqif_eq _)).
by rewrite big_cons leUr.
apply/negP=>/eqP/esym/eqP; rewrite big_cons -lehEcup.
move: (projT2 (cid H))=>/=[]+ _.
by rewrite eq_sproj0 lehO=>/negP.
Qed.

Lemma left_nonempty_dim_ge F s n l :
  left_nonempty F s (ohspace_rec F s l n) ->
  (n <= \Dim (\cup_(j <- ohspace_rec F s l n) F j))%N.
Proof.
elim: n l=>[l|n IH l]; first by rewrite /= leq0n.
rewrite ohspace_rec_iterE.
case: asboolP=>// P1 P2; apply: (leq_trans _ (ohspace_rec_dim P1)).
by rewrite ltnS; apply: IH.
Qed.

Lemma left_nonemptyN_dimU F s l :
  ~ left_nonempty F s (ohspace_rec F s l (dim U)).
Proof.
move=>P1; move: {+}P1=>/left_nonempty_dim_ge P2.
have P3: (\cup_(j <- ohspace_rec F s l (dim U)) F j) = `1`.
  by apply/eqP; rewrite eqhEdim leh1/= dimh1.
by move: P1=>[x /=]; rewrite P3 ocompl1 sproj0x eqxx=>[[]].
Qed.

(* rewrite from infinite cups to finite cups, *)
(* since we focus on finite-dimensional cases *)
Lemma ohspace_correct (F : I -> {hspace U}) s :
  \cups_(i in s) F i = \cup_(i <- ohspace F s) F i.
Proof.
apply /le_anti /andP; split; last by
move: (le_cupo_cups F s [::] (dim U)); rewrite /ohspace big_nil joinx0.
apply/left_nonemptyNP/left_nonemptyN_dimU.
Qed.

Lemma supph_cups (F : I -> {hspace U}) P (E : 'CP(U)) : 
  supph (E (\cups_(i in P) F i)) = \cups_(i in P) supph (E (F i)).
Proof.
apply /le_anti /andP; split;
last by apply: cups_glb=> i Pi; apply/supph_lef /cp_preserve_order /cups_sup.
rewrite ohspace_correct; apply: (le_trans (cuphs_supp_le _ _ _ _)).
rewrite big_seq; apply: cuphs_le=> x /ohspace_correct_in.
rewrite inE; apply: cups_sup.
Qed.

Lemma kerh_cups (F : I -> {hspace U}) P (E : 'CP(U)) : 
  kerh (E (\cups_(i in P) F i)) = \caps_(i in P) kerh (E (F i)).
Proof.
rewrite kerhE supph_cups cupsO.
by under eq_capsr do rewrite -kerhE.
Qed.

End supph_cups.

Section bigseq.
Variable (T : choiceType).

(* exchange big *)
Lemma caps_exchange I J (F : I -> J -> {hspace U}) P Q :
  \caps_(i in P) \caps_(j in Q) F i j = \caps_(j in Q) \caps_(i in P) F i j.
Proof.
rewrite -caps_setM; apply: hseq_split=> x;
rewrite !bigcaph.unlock -!extract_correct ?inE /=; try exact: caps_pclosed.
move=> H j Qj; rewrite -extract_correct ?inE /=; try (exact: caps_pclosed);
move=> i Pi; exact: H (i, j) (conj Pi Qj).
move=> H ij [Pi Qj]; move: (H ij.2 Qj); rewrite -extract_correct ?inE /=;
first exact: caps_pclosed; by apply.
Qed.

Lemma cups_exchange I J (F : I -> J -> {hspace U}) P Q:
  \cups_(i in P) \cups_(j in Q) F i j = \cups_(j in Q) \cups_(i in P) F i j.
Proof.
rewrite -cups_setM bigcuph.unlock; f_equal;
under [RHS]eq_capsr do rewrite ocomplK.
by rewrite caps_exchange -caps_setM.
Qed.

Lemma caps_seq_cond (s : seq T) (F : T -> {hspace U}) (P : pred T) :
  \caps_(t in [set x | (x \in s) && P x]) (F t) =
  \cap_(t <- s | P t) (F t).
Proof. 
elim: s => [/=|h s ih]; first by rewrite set_nil caps_set0 big_nil.
rewrite big_cons -ih; apply: hseq_split=> u; rewrite caps_extract /=.
- case: ifPn => Ph H;
  try (apply /memhIP; split; first by apply: H; rewrite mem_head);
  rewrite caps_extract=> x /= /andP [sx Px];
  by rewrite H ?Px ?inE ?sx ?orbT.
- case: ifPn =>[Ph /memhIP [Hhu] | /negP Ph];
  rewrite caps_extract /= =>H x /andP [];
  rewrite inE=> /orP [/eqP ->//| xs] Px;
  by rewrite H ?Px ?inE ?xs.
Qed.

Lemma caps_seq (s : seq T) (f : T -> {hspace U}) :
  \caps_(t in [set` s]) (f t) = \cap_(t <- s) (f t).
Proof.
rewrite -(caps_seq_cond s f xpredT); congr (\caps_(t in mkset _) _).
by rewrite funeqE => t; rewrite andbT.
Qed.

Lemma cups_seq_cond (s : seq T) (f : T -> {hspace U}) (P : pred T) :
  \cups_(t in [set x | (x \in s) && P x]) (f t) =
    \cup_(t <- s | P t) (f t).
Proof. by rewrite bigcuph.unlock caps_seq_cond -cuphsO ocomplK. Qed.

Lemma cups_seq (s : seq T) (f : T -> {hspace U}) :
  \cups_(t in [set` s]) (f t) = \cup_(t <- s) (f t).
Proof. by rewrite bigcuph.unlock caps_seq -cuphsO ocomplK. Qed.

End bigseq.

(* move *)
Lemma trlf1 : \Tr (\1 : 'End(U)) = (dim U)%:R.
Proof.
rewrite (onb_trlf eb); under eq_bigr do rewrite lfunE/= ns_dot.
by rewrite sumr_const card_ord.
Qed.

Lemma supplfZ (c : C) (f : 'End(U)) :
  c != 0 -> supplf (c *: f) = supplf f.
Proof.
by rewrite -hsE -[supplf f]hsE -!/(supph _)=>Pc;
apply/hspacelfP/supphZ.
Qed.

Lemma supphZ_le (c : C) (A : 'End(U)) : 
  supph (c *: A) `<=` supph A.
Proof.
case E: (c == 0).
by move: E=>/eqP->; rewrite scale0r supph0 le0h.
by move: E=>/eqP/eqP/supphZ->.
Qed.

Lemma kerhZ_ge (c : C) (A : 'End(U)) : 
  kerh A `<=` kerh (c *: A).
Proof. by rewrite !kerhE lehO supphZ_le. Qed.

(* generalize to U, V *)
Lemma kerhZ (c : C) (f : 'End(U)) :
  c != 0 -> kerh (c *: f) = kerh f.
Proof. by move=>Pc; apply/ocompl_inj; rewrite -!supphE supphZ. Qed.

Lemma hs_neq0_exists (f : {hspace U}) :
  f != `0` -> exists x : 'NS, (x : U) \in f.
Proof.
rewrite -dimh_eq0 -lt0n=>P1.
have i : 'I_(\Dim f) by case: (\Dim f) P1=>// n _; apply: ord0.
exists (heigen i). apply/heigen_mem.
Qed.

Lemma hsxO_comp (P : {hspace U}) : P \o ~` P = 0.
Proof. by rewrite !hsE projf_cplmtMr. Qed.
Lemma hsOx_comp (P : {hspace U}) : ~` P \o P = 0.
Proof. by rewrite !hsE projf_cplmtMl. Qed.

End CapsCups.
Local Open Scope hspace_scope.

Lemma heigenUE (U : chsType) (A : {hspace U}) : 
  A = \cup_i <[(@heigen _ A i)]>.
Proof. rewrite -[LHS]supph_id; exact: supph_eigenU. Qed.

Lemma sprojh_memJE (U : chsType) (A B : {hspace U}) (v : U) :
  v \in (A `&&` B) -> B v == 0 = (v == 0).
Proof.
rewrite /sasaki_projection memhI memhE
  => /andP [] /eqP P1 /memhUP =>[[v1 +][v2 + Pv]];
rewrite memhOE ocomplK memhE=>/eqP P3 /eqP P4.
move: P1; rewrite {1}Pv linearD/= P3 add0r=>P5.
by rewrite -{1}P5 -P4 -comp_lfunE -comp_lfunE -[in X in _ \o X](hermf_adjE B) 
  -formsoE -psdf_dot_eq0E/= formsoE !comp_lfunE
  -adj_dotEl psdf_dot_eq0E hermf_adjE P4 P5.
Qed. 

Lemma nonincreaing_nat_lim (f : nat -> nat) :
  (nonincreasing_seq f) -> exists n N, forall i, (N <= i)%N -> (f i = n).
Proof.
set x := f 0%N; have: f 0%N = x by [].
move: x=>x; elim/ltn_ind: x f => i0 IH f P0 Pf.
move: (EM (exists i, f i < i0)%N)=>[[i Pi]|].
pose g j := f (j + i)%N.
have Pg0: (g 0 < i0)%N by rewrite /g add0n.
have : {homo g : n m0 / (n <= m0)%N >-> (m0 <= n)%N}.
  by move=>a b Pab; rewrite /g; apply/Pf; rewrite leq_add2r.
move=>/(IH _ Pg0 g erefl)[] n [] j Pj.
  exists n; exists (i + j)%N => k Pk.
  rewrite -(@subnK i k); first by apply/(leq_trans _ Pk)/leq_addr.
  by rewrite -/(g _) Pj// leq_subRL//; apply/(leq_trans _ Pk)/leq_addr.
rewrite -forallNP=>Pi; exists i0; exists 0%N=>i /Pf.
move: (Pi i)=>/negP; rewrite -leqNgt P0=>P1 P2.
by apply/le_anti/andP.
Qed.

Lemma leh_kerhP (U V : chsType) (f : 'Hom(U,V)) (P : {hspace U}) :
  f \o P = 0 -> P `<=` kerh f.
Proof.
by move=>P1; apply/lehP=>x; rewrite memhE memh_kerE=>/eqP<-;
rewrite -comp_lfunE P1 lfunE.
Qed.

Lemma comp_kerh (U V : chsType) (f : 'Hom(U,V)) : f \o kerh f = 0.
Proof.
by rewrite kerhE !hsE/= !hsE/= /cplmt
  linearBr/= suppvlf comp_lfun1r subrr.
Qed.

Lemma kerh_limn (U : chsType) (f : nat -> 'End(U)) :
  cvgn f -> nondecreasing_seq f -> (forall i, f i \is psdlf) ->
    kerh (limn f) = \caps_(i : nat) kerh (f i).
Proof.
move=>cf nc Pi.
have: [set x : 'End(U) | x \is psdlf]%classic (limn f).
  apply: (@closed_cvg _ _ _ eventually_filter f _ _ _ _)=>//.
  apply closed_psdlf. by apply: nearW=>x/=; apply: Pi.
rewrite/==>Pf.
apply/le_anti/andP; split.
  rewrite -lehO -supphE capsO; apply/cups_glb=>i _.
  rewrite -supphE (PsdLf_BuildE (Pi _)) (PsdLf_BuildE Pf) supph_lef=>[/=|//].
  apply: (nondecreasing_cvgn_lev nc cf).
pose fd i := \Dim (kerh (f i)).
have nfd : nonincreasing_seq fd.
  by move=>m n /nc; rewrite /fd (PsdLf_BuildE (Pi _)) 
    ((PsdLf_BuildE (Pi n)))=>/kerh_lef/dimh_le.
move: (nonincreaing_nat_lim nfd)=>[d [n] Pd].
suff P1 : forall i : nat, (n <= i)%N -> f i \o kerh (f n) = 0.
suff /leh_kerhP : limn f \o kerh (f n) = 0.
  by apply/le_trans; apply: caps_inf.
rewrite -lfun_comp_liml//.
apply: lim_near_cst=>//; by exists n.
move=>i Pn; rewrite -(comp_kerh (f i)); f_equal; apply/eqP.
move: (nc _ _ Pn); rewrite (PsdLf_BuildE (Pi _)) ((PsdLf_BuildE (Pi i))).
move=>/kerh_lef/dimh_leqif_eq/=/leqifP; case: eqP=>[->//|_].
by move: (Pd _ (leqnn n)) (Pd _ Pn); rewrite /fd=>->->; rewrite ltnn.
Qed.
