From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra finmap finalg.
From mathcomp.analysis Require Import -(notations)forms.
From mathcomp.classical Require Import boolp classical_sets.
From mathcomp.analysis Require Import reals exp trigo normedtype derive topology.
(* From mathcomp.real_closed Require Import complex. *)
From quantum.external Require Import complex.
From mathcomp.real_closed Require Import mxtens.

Require Import mcextra mcaextra hermitian.
Require Import mxpred extnum ctopology quantum inhabited.

Import Order.TTheory GRing.Theory Num.Theory Num.Def.
Import VectorInternalTheory.
Import numFieldNormedType.Exports.

(************************************************************************)
(*                    Utility for data type                             *)
(* Define the frequently used structures for quantum programs           *)
(* includes :                                                           *)
(*   basic states and gates for qubits :                                *)
(*           '0 , '1 : computational basis of qubit 'Hs bool            *)
(*    '+ , '- , '±b : superposition state |+> |->                       *)
(*   ''X , ''Y , ''Z : Pauli gates X Y Z                                *)
(*         ''S , ''H : Hadamard gate, phase gate                        *)
(*      'ph , PhGate : parameterized phase state and phase gate         *)
(*   'Rx , 'Ry , 'Rz : rotation gate over x,y,z axes                    *)
(*          (U ⊕ V) : qubit Multiplexer                                *)
(*              ''CU : controlled unitary                               *)
(*        ''CZ, CNOT : controlled-Z gate, CNOT gate                     *)
(*   partial unitary :                                                  *)
(*      PUnitary u v : u v : PONBasis. construct unitary from two ponb  *)
(*                     basis the extendd unitary for \sum_i |v i><u i| *)
(*                     i.e., U : |u i> |-> |v i>                        *)
(*      VUnitary u v : u v : 'NS('Hs T). cextendd unitary for          *)
(*                     [> v ; u <]; i.e., U : u |-> v                   *)
(*                     i.e., U : |u i> |-> |v i>                        *)
(*   General gates and states for abstract data type :                  *)
(*          uniformtv : uniform states                                  *)
(*                'Hn : unitary map |witness> to uniformtv              *)
(*      Multiplexer f : quantum multiplexer built from                  *)
(*                      f : T1 -> 'End[T2]                              *)
(*           QFTv QFT : quantum fourier basis and transformation        *)
(*                      on ordinal number 'I_n.+1                       *)
(*           Oracle f : |t1>|t2> |-> |t1>|t2+f(t1)>                     *)
(*                      f : T1 -> T2; T2 is finZmodType                 *)
(*         PhOracle f : |t> |-> (-1)^(f t)|t>; f : pred T               *)
(*               SWAP : swap gate of  T * T                             *)
(************************************************************************)

Local Notation C := hermitian.C.
Local Notation R := hermitian.R.
Local Open Scope ring_scope.
Local Open Scope fset_scope.
Local Open Scope lfun_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Lemma natrS_neq0 (T : numDomainType) n : (n.+1%:R : T) != 0.
Proof. by rewrite pnatr_eq0. Qed.
Global Hint Extern 0 (is_true (_.+1%:R != 0)) => solve [apply: natrS_neq0] : core.
Global Hint Extern 0 (is_true (0 <= _%:R)) => solve [apply: ler0n] : core.
Global Hint Extern 0 (is_true (0 < _.+1%:R)) => solve [apply: ltr0Sn] : core.
Lemma natr_nneg (F : numDomainType) n : (n%:R : F) \is Num.nneg.
Proof. by rewrite nnegrE. Qed.
Global Hint Extern 0 (is_true (_%:R \is Num.nneg)) => solve [apply: natr_nneg] : core.

Global Hint Resolve leq_ord : core.
Global Hint Extern 0 (is_true (uniq (index_enum _))) => solve [apply: index_enum_uniq] : core.

Local Open Scope ring_scope.

HB.instance Definition _ (T : finZmodType) := isPointed.Build T 0.

Section ExpTrigoDef.

Definition expi (x : R) := (cos x +i* sin x)%C.
Lemma expi0 : expi 0 = 1. Proof. by rewrite /expi cos0 sin0. Qed.
Lemma expiD (x y : R) : expi (x + y) = expi x * expi y.
Proof. by rewrite /expi cosD sinD; simpc; f_equal; rewrite addrC. Qed.
Lemma expiN (x : R) : expi (- x) = (expi x)^-1.
Proof. by rewrite /expi /GRing.inv/= cos2Dsin2 !divr1 cosN sinN. Qed.

End ExpTrigoDef.

HB.lock
Definition expip (x : R) : C := expi (pi * x).
HB.lock
Definition sinp (x : R) : R := sin (pi * x).
HB.lock
Definition cosp (x : R) : R := cos (pi * x).
Canonical expip_unlockable := Unlockable expip.unlock.
Canonical sinp_unlockable := Unlockable sinp.unlock.
Canonical cosp_unlockable := Unlockable cosp.unlock.

Section ExpTrigoDef.

(* we absorb pi into exp sin and cos. to work on rational number *)
(* set up theories on rat - C *)
(* remark: there already some automation of rat, ring_theory and field_theory *)

Lemma expipD (x y : R) : expip (x + y) = expip x * expip y.
Proof. by rewrite !unlock /expip -expiD -mulrDr/=. Qed.
Lemma expipN (x : R) : expip (- x) = (expip x)^-1.
Proof. by rewrite !unlock /expip -expiN mulrN. Qed.
Lemma expipNC (x : R) : expip (- x) = (expip x)^*.
Proof. by rewrite !unlock /expi; simpc; rewrite cosN sinN. Qed.
Lemma expipB (x y : R) : expip (x - y) = expip x / expip y.
Proof. by rewrite expipD expipN. Qed.
Lemma expip0 : expip 0 = 1. Proof. by rewrite !unlock /expip mulr0 expi0. Qed.
Lemma expip1 : expip 1 = -1. 
Proof. by rewrite !unlock /expip mulr1 /expi cospi sinpi; simpc. Qed.
Lemma expip2 : expip 2%:R = 1. 
Proof.
rewrite !unlock /expip /expi mulr_natr -[_*+2]mulr1n -[_*+_*+_]add0r 
  !periodicn ?cos0 ?sin0//. apply cosD2pi. apply sinD2pi.
Qed.
Lemma expip_half : expip ((2%:R)^-1) = 'i.
Proof. by rewrite !unlock /expip /expi cos_pihalf sin_pihalf. Qed.
Lemma expipX (r : R) (n : nat) : expip (r * n%:R) = (expip r) ^+ n.
Proof.
elim: n=>[|n IH]. by rewrite mulr0 expr0 expip0.
by rewrite -{1}addn1 natrD mulrDr expipD mulr1 IH exprSr.
Qed.
Lemma expip2n (n : nat) : expip ((2 * n)%:R) = 1.
Proof. by rewrite natrM expipX expip2 expr1n. Qed.
Lemma expip_prod I (r : seq I) (P : pred I) (f : I -> R):
  \prod_(i <- r | P i) expip (f i) = expip (\sum_(i <- r | P i) f i).
Proof. by elim/big_rec2: _=>[|i?? _ ->]; rewrite ?expip0//expipD. Qed.

Lemma periodicN [U V : zmodType] [f : U -> V] [T : U] :
  periodic f T -> periodic f (-T).
Proof. by move=> + u => /(_ (u - T)); rewrite addrNK => /esym. Qed.

Lemma periodicz [U V : zmodType] [f : U -> V] [T : U] :
  periodic f T -> forall (n : int) (a : U), f (a + T *~ n) = f a.
Proof.
move=> prd_f [] /= n; first by rewrite -pmulrn; apply: periodicn.
move=> u; rewrite NegzE -nmulrn -mulNrn.
by apply/periodicn/periodicN.
Qed.

Lemma cos_eq1 (x : R) : `|x| < pi * 2%:R -> cos x = 1 -> x = 0.
Proof.
suff wlog: forall (y : R), 0 <= y < pi * 2%:R -> cos y = 1 -> y = 0.
- case: (lerP 0 x) => [ge0_x|/ltW le0_x].
  - by rewrite ger0_norm // => ?; apply: wlog; apply/andP; split.
  - rewrite ltr_norml => /andP[+ _]; rewrite ltrNl -cosN => bd_Nx.
    move/wlog; rewrite bd_Nx oppr_ge0 le0_x /= => /(_ (erefl true)).
    by rewrite (rwP eqP) oppr_eq0 => /eqP ->.
move=> {}x bd_x; case: (lerP x pi) => [le_x_pi|le_pi_x].
- rewrite -cos0 => /cos_inj; apply; rewrite in_itv /=.
  - by rewrite le_x_pi andbT; case/andP: bd_x.
  - by rewrite lexx /= pi_ge0.
- move=> /(congr1 -%R); rewrite -cosDpi -(periodicz (@cosD2pi _) (-1)).
  rewrite mulrN1z mulr2n opprD addrA addrK -cospi.
  move/cos_inj; rewrite !in_itv /=.
  rewrite pi_ge0 lexx /= subr_ge0 [pi <= x]ltW //=.
  rewrite lerBlDr -mulr2n -mulr_natr.
  case/andP: (bd_x) => _ /ltW -> /(_ (erefl true) (erefl true)).
  move/(congr1 (fun x => x + pi)); rewrite subrK -mulr2n -mulr_natr => xE.
  by case/andP: bd_x => _; rewrite xE ltxx.
Qed.

Section IsDeriveV.
Variables (R : numFieldType) (V : normedModType R).

Global Instance is_deriveV (f : V -> R) (x v : V) (df : R) :
     f x != 0
  -> is_derive x v f df
  -> is_derive x v (fun x => (f x)^-1) (- (f x) ^- 2 * df).
Proof.
move=> nz_fx dfx; apply: DeriveDef; first exact: derivableV.
by rewrite deriveV // !derive_val.
Qed.
End IsDeriveV.

Section IsDeriveDiv.
Variables (R : numFieldType) (V : normedModType R).

Lemma derive_div (f g : V -> R) (x v : V) :
     g x != 0
  -> derivable f x v
  -> derivable g x v
  -> derivable (fun y => f y / g y) x v.
Proof.
move=> nz_gx df dg; apply: derivableM; first exact df.
by apply: derivableV.
Qed.

Global Instance is_derive_div (f g : V -> R) (x v : V) (df dg : R) :
     g x != 0
  -> is_derive x v f df
  -> is_derive x v g dg
  -> is_derive x v (fun y => f y / g y) ((g x) ^- 2 * (df * g x - f x * dg)).
Proof.
move=> nz_g dfv dgv; have dgIv := is_deriveV nz_g dgv.
move: (is_deriveM dfv dgIv); set d := (X in is_derive _ _ _ X -> _).
move=> h; set d' := (X in is_derive _ _ _ X).
(suff ->//: d' = d by apply: h); rewrite {h}/d {}/d'.
rewrite /GRing.scale /= !(mulNr, mulrN) [RHS]addrC mulrBr.
congr (_ - _); last by rewrite mulrCA.
rewrite mulrA [LHS]mulrAC; congr (_ * _).
by rewrite mulrC expr2 invfM mulrCA divff // mulr1.
Qed.
End IsDeriveDiv.

Lemma pi_gt1 : 1 < pi :> R.
Proof. by apply:(lt_le_trans _ (pi_ge2 R)) => //; rewrite (natrD _ 1 1) ltrDl. Qed.

Lemma pi_le4 : pi <= 4%:R :> R.
Proof.
rewrite /pi; case xgetP => /= [x _ | _]; last by rewrite mul0rn.
case=> /andP[_ le2_x] _; rewrite mulr2n -[4%:R]/(2+2)%:R.
by rewrite natrD lerD.
Qed.

Lemma ger_tan x : x \in `[0, pi / 2%:R[ -> x <= tan x :> R.
Proof.
rewrite in_itv /= => /andP[+ lt_pihalf].
rewrite le_eqVlt => /orP[/eqP<-|gt0_x]; first by rewrite tan0.
have le2_x: x <= 2%:R.
- apply/ltW/(lt_le_trans lt_pihalf); rewrite ler_pdivrMr //.
  by rewrite -natrM /= pi_le4.
have nz_cos c: c \in `[0, x] -> cos c != 0.
- rewrite in_itv /= => /andP[gt0_c le_cx].
  apply/contraL: (lt_pihalf) => /eqP z_cosc.
  rewrite -leNgt; have <-// := @cos_02_uniq _ c (pi / 2%:R).
  - by rewrite gt0_c //= (le_trans le_cx).
  - rewrite mulr_ge0 //= ?(invr_ge0, pi_ge0) //.
    by rewrite ler_pdivrMr // -natrM pi_le4.
  - by rewrite cos_pihalf.
have dt: forall y, y \in `]0, x[ -> is_derive y 1 tan (cos y ^- 2).
- move=> y rg_y; apply: is_derive_tan.
  by apply: nz_cos; apply: subset_itv rg_y.
have ct: {within `[0, x], continuous tan}%classic.
- apply: continuous_in_subspaceT=>c; rewrite mem_setE /= => rg_c.
  by apply/continuous_tan/nz_cos; apply: subset_itv rg_c.
have [d +] := MVT gt0_x dt ct; rewrite in_itv /= => /andP[gt0_d lt_dx].
rewrite tan0 !subr0 => ->; rewrite ler_peMl //; first by apply/ltW.
rewrite invf_ge1; last first.
- rewrite exprn_ile1 // (cos_le1, cos_ge0_pihalf) //.
  by rewrite -ler_norml gtr0_norm // ltW // (lt_trans lt_dx).
rewrite exprn_gt0 // cos_gt0_pihalf // -ltr_norml gtr0_norm //.
by rewrite (lt_trans lt_dx).
Qed.

Lemma ler_abs_sin (a : R) : `|sin a| <= `|a|.
suff wlog: forall (a : R), 0 <= a <= 1 -> sin a <= a.
- case: (lerP 1 `|a|) => [|lt1_a].
  - by move=> le; apply: (le_trans (sin_max a) le).
  wlog: a lt1_a / (0 <= a) => [{}wlog|ge0_a].
  case: (ler0P a) => [|/ltW ge0_a]; last first.
  - by rewrite -[X in _ <= X]ger0_norm //; apply: wlog.
  move=> le0_a; have := wlog (-a).
  rewrite normrN oppr_ge0 => /(_ lt1_a le0_a).
  by rewrite sinN normrN [ `|a|]ler0_norm.
  rewrite !ger0_norm //; last first.
  - by apply/wlog/andP; split=> //; apply/ltW/ltr_normlW.
  apply/sin_ge0_pi; rewrite ge0_a /= (@le_trans _ _ 1) //.
  - by apply/ltW/ltr_normlW.
  - by apply/ltW/pi_gt1.
move=> {}a /andP[+ le1_a]; rewrite le_eqVlt => /orP[|lt0_a].
- by move/eqP=> <-; rewrite sin0.
have := @MVT R sin cos 0 a lt0_a (fun x _ => is_derive_sin x).
case; first by apply/continuous_subspaceT/continuous_sin.
move=> c rg_c; rewrite sin0 !subr0 => ->.
by rewrite ler_piMl //; [apply/ltW | apply/cos_le1].
Qed.

Lemma ger_abs_sin (a : R) : `|a| <= pi / 2%:R -> (2%:R * `|a| / pi) <= `|sin a|.
Proof.
wlog: a / (0 <= a) => [wlog|ge0_a].
- case: (ler0P a) => [le0_a|/ltW ge0_a]; last first.
  - by have := wlog a ge0_a; rewrite ger0_norm.
  move=> bd_a; rewrite -ler0_norm //.
  have := wlog (-a); rewrite oppr_ge0 sinN !normrN.
  by apply=> //; rewrite ler0_norm.
rewrite [ `|a|]ger0_norm // => bd_a; rewrite ger0_norm.
- apply: sin_ge0_pi; rewrite ge0_a /=; apply: (le_trans bd_a).
  rewrite ler_pdivrMr // ler_pMr ?pi_gt0 //.
  by rewrite (natrD _ 1 1) lerDl.
move: ge0_a; rewrite le_eqVlt => /orP[/eqP <-|gt0_a].
- by rewrite !Monoid.simpm sin0.
move: bd_a; rewrite le_eqVlt => /orP[/eqP->|bd_a].
- rewrite sin_pihalf mulrAC -[pi / _]invf_div divff //.
  by rewrite mulf_neq0 //= invr_eq0 gt_eqF // pi_gt0.
pose f (x : R) := sin x / x.
pose F (x : R) := (x * cos x - sin x) / (x ^+ 2).
have fF (c : R): c \in `[a, pi / 2%:R] -> is_derive c 1 f (F c).
- rewrite in_itv /= => /andP[lt_ac lt_c_pi].
  have nz_c: c != 0 by rewrite gt_eqF // (lt_le_trans gt0_a).
  have := @is_derive_div R R sin idfun c 1 (cos c) 1 nz_c (is_derive_sin c) (is_derive_id c 1).
  set d := (X in is_derive _ _ _ X -> _) => h; suff <-: d = F c by done.
  by rewrite {h}/d {}/F /= [LHS]mulrC mulr1 [c * cos c]mulrC.
have h1 (c : R): c \in `]a, pi / 2%:R[ -> is_derive c 1 f (F c).
- by move=> rg_c; apply: fF; apply: subset_itv rg_c.
have h2: {within `[a, pi / 2%:R], continuous f}%classic.
  (* this should be a direct consequence of `fF`! *)
- apply: continuous_in_subspaceT => c rg_c.
  apply: cvgM; first by apply: continuous_sin.
  apply: cvgV; last by apply: cvg_id.
  move: rg_c; rewrite mem_setE in_itv /= => /andP[+ _].
  by apply: contraL => /eqP->; rewrite -ltNge.
have {h1 h2 fF}[c] := @MVT R f F a (pi / 2%:R) bd_a h1 h2.
rewrite in_itv /= => /andP[lt_ac bd_c]; rewrite {}/f {}/F.
rewrite sin_pihalf invf_div mul1r (rwP eqP) subr_eq.
rewrite [_ + (sin a / a)]addrC -subr_eq => /eqP /esym sinaVaE.
rewrite mulrAC -ler_pdivlMr // {}sinaVaE lerBrDl.
rewrite ler_wnDl //; apply: mulr_le0_ge0; last first.
- by rewrite subr_ge0; apply/ltW.
apply: mulr_le0_ge0; last first.
- by rewrite invr_ge0 exprn_ge0 //; apply/ltW/(lt_trans gt0_a).
rewrite subr_le0; rewrite -ler_pdivlMr.
- apply: cos_gt0_pihalf; rewrite -ltr_norml ger0_norm //.
  by apply/ltW/(lt_trans gt0_a).
rewrite -/(tan c); apply: ger_tan; rewrite in_itv /=.
by rewrite !ltW // (lt_trans gt0_a).
Qed.

Lemma pi_neq0 : (pi : R) != 0.
Proof. by move: (pi_gt0 R)=>/lt0r_neq0/negPf->/=. Qed.

Lemma pi_eq0 : (pi : R) == 0 = false.
Proof. apply/eqP/eqP/pi_neq0. Qed.

Lemma expip_sum_cst n r :
  expip r = 1 -> \sum_(k < n) expip (r * k%:R) = n%:R.
Proof. by move=>P; under eq_bigr do rewrite expipX P expr1n; rewrite sumr_const card_ord. Qed.

Lemma expip_sum n r :
  expip r != 1 -> \sum_(k < n) expip (r * k%:R) = (1 - expip (r * n%:R)) / (1 - expip r).
Proof.
rewrite -subr_eq0=>/eqP/eqP=>P; apply/(mulfI P); under eq_bigr do rewrite expipX.
by rewrite -subrX1 expipX mulrC -[X in _ / X]opprB invrN mulrN mulNr mulfVK// opprB.
Qed.

Lemma expip_eq1_uniq r : `|r| < 2%:R -> expip r = 1 -> r = 0.
Proof.
move=>Pr; have P1: `|pi * r| < pi * 2%:R 
  by rewrite normrM ger0_norm ?pi_ge0// ltr_pM2l// ?pi_gt0.
rewrite unlock /expi=>P2; inversion P2.
by move: (cos_eq1 P1 H0)=>/eqP; rewrite mulf_eq0 pi_eq0/==>/eqP.
Qed.

Lemma expip_neq1 r : `|r| < 2%:R -> r != 0 -> expip r != 1.
Proof. by move=>/expip_eq1_uniq P1; apply contraNN=>/eqP/P1->. Qed.

Lemma expip_sum_ord (m n : nat) (i j : 'I_m) : (m <= n)%N ->
  \sum_(k < n) expip (2%:R * (i%:R - j%:R) * k%:R / n%:R) = ((i == j))%:R * n%:R.
Proof.
under eq_bigr do rewrite mulrC mulrA.
case: eqP=>[->|]; first by rewrite expip_sum_cst ?mul1r// subrr !mulr0 expip0.
move=>/eqP P1 P2; case: n P2=>[_|n P2]; first by rewrite big_ord0 mulr0.
rewrite expip_sum; first apply/expip_neq1.
rewrite !normrM 2?ger0_norm ?invr_ge0 ?ler0n// ltr_pdivrMl ?ltr0n// 
  mulrC ltr_pM2r ?ltr0n// lter_distl ltrBlDl addrC; apply/andP; 
  by split; apply/ltr_wpDl; rewrite ?ler0n// ltr_nat; apply: (leq_trans _ P2).
by rewrite !mulf_eq0 invr_eq0 !negb_or !natrS_neq0/= subr_eq0 eqr_nat.
by rewrite mulrC mulfVK ?natrS_neq0// mulrBr 
  expipB -!natrM !expip2n invr1 mulr1 subrr mul0r mul0n.
Qed.

Lemma expip_period n r : expip ( (2 * n)%:R + r) = expip r.
Proof.
rewrite unlock mulrDr natrM mulrA !mulr_natr addrC /expi.
rewrite !periodicn//. apply cosD2pi. apply sinD2pi.
Qed.

End ExpTrigoDef.

Section trigoExtra.
Implicit Type (x y z : R).
Local Notation "2" := (2%:R : R).

Lemma sinB x y : sin (x - y) = sin x * cos y - cos x * sin y.
Proof. by rewrite sinD cosN sinN mulrN. Qed.
Lemma cosB x y : cos (x - y) = cos x * cos y + sin x * sin y.
Proof. by rewrite cosD cosN sinN mulrN opprK. Qed.

Lemma sin2x x : sin (x *+ 2) = (sin x * cos x) *+ 2.
Proof. by rewrite mulr2n sinD [cos _* _]mulrC -mulr2n -mulr_natl mulrA. Qed.
Lemma cos2x x : cos (x *+ 2) = (cos x) ^+ 2 - (sin x) ^+ 2.
Proof. by rewrite mulr2n cosD -!expr2. Qed.
Lemma cos2x_cos x : cos (x *+ 2) = ((cos x) ^+ 2) *+ 2 - 1.
Proof. by rewrite cos2x -(cos2Dsin2 x) mulr2n opprD addrACA subrr add0r. Qed.
Lemma cos2x_sin x : cos (x *+ 2) = 1 - ((sin x) ^+ 2) *+ 2.
Proof. by rewrite cos2x -(cos2Dsin2 x) mulr2n opprD addrACA subrr addr0. Qed.

End trigoExtra.

Lemma bigfcup0 (L : choiceType) I (r : seq I) (P : pred I) :
  \bigcup_(i <- r | P i) fset0 = (fset0 : {fset L}).
Proof.
elim: r=>[|x r IH]; first by rewrite big_nil.
by rewrite big_cons; case: (P x)=>//; rewrite IH fsetU0.
Qed.

Lemma eqbbb (b : bool) : (b == b) = true. Proof. by rewrite eqxx. Qed.
Lemma eqbTF : (true == false) = false. Proof. by []. Qed.
Lemma eqbFT : (false == true) = false. Proof. by []. Qed.
Definition simpb := (eqbbb, eqbTF, eqbFT, andbT, andbF, orbT, orbF).
Definition simp01 := (mulr0, mul0r, subr0, sub0r, addr0, add0r, 
  mulr1, mul1r, oppr0, expr1, expr0, expr0z, expr1z, eqxx).

Lemma ffunfb_eq (f g : bool -> bool -> C) :
    [/\ f true true = g true true , f true false = g true false , 
    f false true = g false true & f false false = g false false] -> 
    mx2tf f = mx2tf g.
Proof.
by move=>[P1 P2 P3 P4]; apply/mx2tfP=>b1 b2; case: b1; case: b2.
Qed.

Lemma ffunvb_eq (f g : bool -> C) :
    (f true = g true /\ f false = g false) -> mv2tv f = mv2tv g.
Proof.
by move=>[P1 P2]; apply/mv2tvP=>y; by case: y.
Qed.

Notation "[ 'bmx' [ b11 , b12 ] ; [ b21 , b22 ] ]" :=
  (mx2tf (fun x y => match x,y with 
  | false , false => b11
  | false , true => b12
  | true , false => b21
  | true , true => b22
  end
  )).
Notation "[ 'bmx' b11 , b12 ; b21 , b22 ]" :=
  [bmx [b11 , b12] ; [b21 , b22]].
Notation "[ 'bmv' b1 ; b2 ]" := (mv2tv (fun x=> 
  match x with | false => b1 | true => b2 end)).

Ltac rude_bmx := rewrite /t2tv ?tf2mxE; do ? [apply/ffunfb_eq | apply/ffunvb_eq | f_equal];
    unfold_funfv; (do 4? split); rewrite ?(big_bool)/=;
    do ? rewrite (simpb, simp01)/=.


Section BoolGates.

Definition Hadamard : 'End('Hs bool) := 
  [bmx 1/sqrtC(2%:R) , 1/sqrtC(2%:R) ; 1/sqrtC(2%:R) , -1/sqrtC(2%:R)].

Definition PauliX : 'End('Hs bool) := [bmx 0 , 1 ; 1 , 0].
Definition PauliY : 'End('Hs bool) := [bmx 0 , -'i ; 'i , 0].
Definition PauliZ : 'End('Hs bool) := [bmx 1 , 0 ; 0 , -1].
Notation "'''H'" := Hadamard.
Notation "'''X'" := PauliX.
Notation "'''Y'" := PauliY.
Notation "'''Z'" := PauliZ.

Lemma Hadamard_unitary : Hadamard \is unitarylf.
Proof. by apply/unitarylfP; rude_bmx; rewrite !divc_simp ?sign_simp// split2. Qed.
HB.instance Definition _ := isUnitaryLf.Build ('Hs bool) Hadamard Hadamard_unitary.

Lemma PauliX_unitary : PauliX \is unitarylf.
Proof. by apply/unitarylfP; rude_bmx. Qed.
HB.instance Definition _ := isUnitaryLf.Build ('Hs bool) PauliX PauliX_unitary.

Lemma PauliY_unitary : PauliY \is unitarylf.
Proof. by apply/unitarylfP; rude_bmx; simpc. Qed.
HB.instance Definition _ := isUnitaryLf.Build ('Hs bool) PauliY PauliY_unitary.

Lemma PauliZ_unitary : PauliZ \is unitarylf.
Proof. by apply/unitarylfP; rude_bmx; simpc. Qed.
HB.instance Definition _ := isUnitaryLf.Build ('Hs bool) PauliZ PauliZ_unitary.

Definition pmbasis (b : bool) : 'Hs bool :=
  [bmv 1/sqrtC(2%:R) ; (-1)^b * 1/sqrtC(2%:R)].
Notation "''0'" := (t2tv false) (at level 0).
Notation "''1'" := (t2tv true) (at level 0).
Notation "''+'" := (pmbasis false) (at level 0).
Notation "''-'" := (pmbasis true) (at level 0).
Notation "''±' b" := (pmbasis b) (at level 2, format "''±' b").

Lemma pmbasis_onb b1 b2 : [<'± b1 ; '± b2>] = (b1 == b2)%:R.
Proof. by rude_bmx; case: b1; case: b2; rewrite !simpb !divc_simp ?sign_simp// split2. Qed.
HB.instance Definition _ := isONB.Build ('Hs bool) bool pmbasis pmbasis_onb (ihb_dim _).

Lemma pmbasis_ns b : [<'± b ; '± b>] == 1%:R.
Proof. by rewrite onb_dot eqxx. Qed.
HB.instance Definition _ b := isNormalState.Build ('Hs bool) (pmbasis b) (eqP (@pmbasis_ns b)).

Lemma dotp_cbpm (b1 b2 : bool) : [<''b1 ; '±b2 >] = (-1)^(b1 && b2) / sqrtC 2%:R.
Proof. by case: b1; case: b2; rude_bmx; rewrite// !sign_simp. Qed.

Lemma dotp_pmcb (b1 b2 : bool) : [<'±b1 ; ''b2 >] = (-1)^(b1 && b2) / sqrtC 2%:R.
Proof. by case: b1; case: b2; rude_bmx; rewrite !divc_simp// !sign_simp. Qed.

Definition Uniform : 'End('Hs bool) := 
  [bmx (2%:R)^-1 , (2%:R)^-1 ; (2%:R)^-1 , (2%:R)^-1].

Lemma plus_uniform : Uniform = [> '+ ; '+ <].
Proof. by rude_bmx; rewrite !divc_simp. Qed.

Lemma Uniform_den : Uniform \is denlf.
Proof. by rewrite plus_uniform is_denlf. Qed.
HB.instance Definition _ := isDenLf.Build ('Hs bool) Uniform Uniform_den.

Ltac unfoldlf := rewrite /Hadamard /PauliX 
  /PauliY /PauliZ /t2tv /pmbasis /Uniform.

Lemma Hadamard_adj : ''H^A = ''H.
Proof. by unfoldlf; rude_bmx; rewrite !divc_simp// !sign_simp. Qed.
Lemma Hadamard_tr : (''H^T)%VF = ''H.
Proof. by unfoldlf; rude_bmx. Qed.
Lemma Hadamard_conj : ''H^C = ''H.
Proof. by rewrite conjfAT Hadamard_adj Hadamard_tr. Qed.
Lemma Hadamard_id : ''H \o ''H = \1.
Proof. by rewrite -{1}Hadamard_adj; apply/unitarylfP/is_unitarylf. Qed.
Lemma HadamardK : cancel ''H ''H.
Proof. by move=>x; rewrite -[RHS]id_lfunE -Hadamard_id lfunE/=. Qed.

Lemma PauliX_adj : ''X^A = ''X.
Proof. by unfoldlf; rude_bmx. Qed.
Lemma PauliX_tr : (''X^T)%VF = ''X.
Proof. by unfoldlf; rude_bmx. Qed.
Lemma PauliX_conj : ''X^C = ''X.
Proof. by rewrite conjfAT PauliX_adj PauliX_tr. Qed.
Lemma PauliX_id : ''X \o ''X = \1.
Proof. by rewrite -{1}PauliX_adj; apply/unitarylfP/is_unitarylf. Qed.
Lemma PauliXK : cancel ''X ''X.
Proof. by move=>x; rewrite -[RHS]id_lfunE -PauliX_id lfunE/=. Qed.

Lemma PauliY_adj : ''Y^A = ''Y.
Proof. by unfoldlf; rude_bmx=>//; simpc. Qed.
Lemma PauliY_tr : (''Y^T)%VF = - ''Y.
Proof. by unfoldlf; rude_bmx=>//; rewrite opprK. Qed.
Lemma PauliY_conj : ''Y^C = - ''Y.
Proof. by rewrite conjfAT PauliY_adj PauliY_tr. Qed.
Lemma PauliY_id : ''Y \o ''Y = \1.
Proof. by rewrite -{1}PauliY_adj; apply/unitarylfP/is_unitarylf. Qed.
Lemma PauliYK : cancel ''Y ''Y.
Proof. by move=>x; rewrite -[RHS]id_lfunE -PauliY_id lfunE/=. Qed.

Lemma PauliZ_adj : ''Z^A = ''Z.
Proof. by unfoldlf; rude_bmx=>//; simpc. Qed.
Lemma PauliZ_tr : (''Z^T)%VF = ''Z.
Proof. by unfoldlf; rude_bmx. Qed.
Lemma PauliZ_conj : ''Z^C = ''Z.
Proof. by rewrite conjfAT PauliZ_adj PauliZ_tr. Qed.
Lemma PauliZ_id : ''Z \o ''Z = \1.
Proof. by rewrite -{1}PauliZ_adj; apply/unitarylfP/is_unitarylf. Qed.
Lemma PauliZK : cancel ''Z ''Z.
Proof. by move=>x; rewrite -[RHS]id_lfunE -PauliZ_id lfunE/=. Qed.

Lemma Hadamard_cb b :  ''H (''b) = '± b.
Proof. by case: b; unfoldlf; rude_bmx. Qed.

Lemma Hadamard_pm b :  ''H ('± b) = ''b.
Proof. by rewrite -Hadamard_cb HadamardK. Qed.

Lemma Hadamard0 : ''H '0 = '+. Proof. exact: Hadamard_cb. Qed.
Lemma Hadamard1 : ''H '1 = '-. Proof. exact: Hadamard_cb. Qed.
Lemma Hadamardplus : ''H '+ = '0. Proof. exact: Hadamard_pm. Qed.
Lemma Hadamardminus : ''H '- = '1. Proof. exact: Hadamard_pm. Qed.

Definition PhGate (r : R) := [bmx 1 , 0 ;  0 , expip r].
Lemma PhGate_unitary r : PhGate r \is unitarylf.
Proof.
apply/unitarylfP; rude_bmx; simpc=>//. 
by rewrite -expipNC -expipD addNr expip0.
Qed.
HB.instance Definition _ (r : R) :=
  isUnitaryLf.Build ('Hs bool) (PhGate r) (@PhGate_unitary r).
Definition PhGate_adj (r : R) : (PhGate r)^A = PhGate (-r).
Proof. by rude_bmx=>//; rewrite -expipNC. Qed.
Definition PhGate_conj (r : R) : (PhGate r)^C = PhGate (-r).
Proof. by rude_bmx=>//; rewrite -expipNC. Qed.
Definition PhGate_tr (r : R) : ((PhGate r)^T)%VF = PhGate r.
Proof. by rude_bmx. Qed.

Definition SGate := PhGate ((2%:R)^-1).

Lemma SGate_cb b : SGate ''b = ('i ^ b) *: ''b.
Proof. by rude_bmx; case: b; rewrite/= ?expr0z ?expr1z ?mulr0// ?expip_half// mulr1. Qed.

Definition phstate (r : R) : ('Hs bool) :=
  [bmv 1/sqrtC(2%:R) ; expip (2%:R * r) * 1/sqrtC(2%:R)].
Notation "''ph' r" := (phstate r) (at level 2, format "''ph'  r").
Lemma phstate_ns r : [<'ph r; 'ph r>] == 1%:R.
Proof.
by rude_bmx; rewrite !divc_simp conjCc -expipNC -expipD addNr 
  expip0 mul1r -mulr2n -mulr_natr mulVf.
Qed.
HB.instance Definition _ (r : R) :=
  isNormalState.Build ('Hs bool) (phstate r) (eqP (@phstate_ns r)).

Lemma phstateE r : 'ph r = (sqrtC 2%:R)^-1 *: '0 + 
  ((sqrtC 2%:R)^-1 * expip (2%:R * r)) *: '1.
Proof. by rude_bmx=>//; rewrite mulrC. Qed.
Lemma dotp_phcb (r : R) b : [< 'ph r ; ''b >] = (sqrtC 2%:R)^-1 * expip (2%:R * b%:R * (-r)).
Proof.
rude_bmx; case: b=>/=; rewrite ?mulr0 !divc_simp ?mul0r ?add0r ?expip0//.
by rewrite !mulr1 addr0 conjCc -expipNC mulrN.
Qed.
Lemma dotp_phcb0 r : [< 'ph r ; '0 >] = ((sqrtC 2%:R)^-1)%R.
Proof. by rewrite dotp_phcb mulr0 mul0r expip0 mulr1. Qed.
Lemma dotp_phcb1 r : [< 'ph r ; '1 >] = (sqrtC 2%:R)^-1 * (expip (2%:R * (-r))).
Proof. by rewrite dotp_phcb mulr1. Qed.

Lemma dotp_cbph b (r : R) : [< ''b ; 'ph r >] = (sqrtC 2%:R)^-1 * expip (2%:R * b%:R * r).
Proof. by rewrite -conj_dotp dotp_phcb !divc_simp conjCc -expipNC mulrN opprK. Qed.
Lemma dotp_cb0ph r : [< '0; 'ph r >] = ((sqrtC 2%:R)^-1)%R.
Proof. by rewrite dotp_cbph mulr0 mul0r expip0 mulr1. Qed.
Lemma dotp_cb1ph r : [< '1; 'ph r >] = (sqrtC 2%:R)^-1 * (expip (2%:R * r)).
Proof. by rewrite dotp_cbph mulr1. Qed.


Lemma conjC_real (x : R) : (x%:C)^* = x%:C.
Proof. by rewrite conjCc !conjc_real. Qed.

Definition FormGate (U : chsType) (x y : R) (f : 'End(U)) := x%:C *: \1 - ('i * y%:C) *: f.
Lemma FormGateE (U : chsType) x y (f : 'End(U)) : 
  x%:C *: \1 - ('i * y%:C) *: f = FormGate x y f.
Proof. by []. Qed.
Lemma FormGate_unitary (U : chsType) x y (f : 'FU(U)) :
  x^+2 + y^+2 = 1 -> f^A = f -> FormGate x y f \is unitarylf.
move=>Pxy Pf. apply/unitarylfP; rewrite /FormGate !linearB/= !linearBl !linearBr/=.
rewrite !adjfZ !adjf1 -!comp_lfunZl -!comp_lfunZr !comp_lfun1l comp_lfun1r.
rewrite unitaryf_form Pf !scalerA !conjcM !conjC_real [_ * ('i * _)]mulrC opprB.
by rewrite conjCi -!scaleNr addrACA -!scalerDl !mulNr addrN mulrACA -!rmorphM/= 
  -!expr2 sqrCi mulN1r opprK -raddfD Pxy/= scale1r scale0r addr0.
Qed.

Definition RxGate (r : R) := (cosp (r / 2%:R))%:C *: \1 - ('i * (sinp (r / 2%:R))%:C) *: PauliX.
Definition RyGate (r : R) := (cosp (r / 2%:R))%:C *: \1 - ('i * (sinp (r / 2%:R))%:C) *: PauliY.
Definition RzGate (r : R) := (cosp (r / 2%:R))%:C *: \1 - ('i * (sinp (r / 2%:R))%:C) *: PauliZ.

Lemma RxGate_unitary r : RxGate r \is unitarylf.
Proof.
rewrite /RxGate FormGateE; apply/FormGate_unitary=>/=.
by rewrite !unlock cos2Dsin2. by rewrite PauliX_adj.
Qed.
HB.instance Definition _ (r : R) :=
  isUnitaryLf.Build ('Hs bool) (RxGate r) (@RxGate_unitary r).
Lemma RyGate_unitary r : RyGate r \is unitarylf.
Proof.
rewrite /RyGate FormGateE; apply/FormGate_unitary=>/=.
by rewrite !unlock cos2Dsin2. by rewrite PauliY_adj.
Qed.
HB.instance Definition _ (r : R) :=
  isUnitaryLf.Build ('Hs bool) (RyGate r) (@RyGate_unitary r).
Lemma RzGate_unitary r : RzGate r \is unitarylf.
Proof.
rewrite /RzGate FormGateE; apply/FormGate_unitary=>/=.
by rewrite !unlock cos2Dsin2. by rewrite PauliZ_adj.
Qed.
HB.instance Definition _ (r : R) :=
  isUnitaryLf.Build ('Hs bool) (RzGate r) (@RzGate_unitary r).

(* write 'i to the end *)
Lemma mulci1 (x : C) : 'i * x = x * 'i. Proof. exact: mulrC. Qed.
Lemma mulci2 : ('i : C)^-1 = - 'i. Proof. exact: invCi. Qed.
Lemma mulci3 : ('i : C)^* = - 'i. Proof. exact: conjCi. Qed.
Lemma mulci4 : ('i : C) * 'i = -1. Proof. by rewrite -expr2 sqrCi. Qed.
Lemma mulci7 (x : C) : x * 'i * 'i = - x. Proof. by rewrite -mulrA mulci4 mulrN1. Qed.
Lemma mulci5 (x y : C) : (x * 'i) * y = (x * y) * 'i. Proof. exact: mulrAC. Qed.
Lemma mulci6 (x y : C) : x * (y * 'i) = (x * y) * 'i. Proof. exact: mulrA. Qed.
Lemma mulci8 (x : R) : (x +i* 0)%C = x%:C. Proof. by []. Qed.
Lemma mulci9 (x : R) : (x*i)%C = x%:C * 'i. Proof. by simpc. Qed.
Definition simp_muli := (mulci2,mulci3,mulci4,mulrN1,mulN1r,mulrN,mulNr,oppcK,mulci1,
  mulci7,mulci5,mulci6,mulci8,mulci9).
Definition real2c := (natrC, realcN, realcD,realcM,realcB,realcMn,realcMNn,
  realcI,realcX,realcXN).

Lemma RxGateD (r1 r2 : R) : (RxGate r1) \o (RxGate r2) = RxGate (r1 + r2).
Proof.
rewrite /RxGate; rude_bmx; rewrite !simp_muli.
2,3: rewrite -opprD -mulrDl; do 2 f_equal.
all: rewrite -!real2c; f_equal; rewrite !unlock.
2,4: rewrite addrC. 1,3: by rewrite -cosD -mulrDr -mulrDl.
all: by rewrite -sinD -mulrDr -mulrDl.
Qed.
Lemma RxGate_adj r : (RxGate r)^A = RxGate (-r).
Proof.
rewrite /RxGate; rude_bmx; rewrite !simp_muli !unlock.
1,4: by rewrite mulrN cosN.
all: by rewrite -[RHS]mulNr -realcN mulrN sinN.
Qed.
Lemma RxGate0 : RxGate 0 = \1.
Proof.
by rewrite /RxGate mul0r [cosp]unlock [sinp]unlock
  mulr0 cos0 sin0 mulr0 scale1r scale0r subr0.
Qed.
Lemma RyGateD (r1 r2 : R) : (RyGate r1) \o (RyGate r2) = RyGate (r1 + r2).
Proof.
rewrite /RyGate; rude_bmx; rewrite !simp_muli -!real2c !unlock; f_equal.
3: rewrite -opprD; f_equal. 2,4: rewrite addrC. 
1,3: by rewrite -cosD -mulrDr -mulrDl.
all: by rewrite -sinD -mulrDr -mulrDl.
Qed.
Lemma RyGate_adj r : (RyGate r)^A = RyGate (-r).
Proof.
rewrite /RyGate; rude_bmx; rewrite !simp_muli !unlock.
all: by rewrite mulrN ?sinN ?cosN// -?realcN// opprK.
Qed.
Lemma RzGateD (r1 r2 : R) : (RzGate r1) \o (RzGate r2) = RzGate (r1 + r2).
Proof.
rewrite /RzGate; rude_bmx; rewrite//!simp_muli.
all: rewrite mulrDr !mulrDl !simp_muli !addrA addrC !addrA -addrA; f_equal.
2,4: by rewrite -?opprD -!mulrDl !unlock -!real2c -sinD -mulrDr mulrDl.
all: by rewrite addrC -!real2c !unlock -cosD -mulrDr.
Qed.
Lemma RzGate_adj r : (RzGate r)^A = RzGate (-r).
Proof.
rewrite /RzGate; rude_bmx; rewrite !simp_muli// !unlock.
all: by simpc; rewrite ?mulrN sinN cosN// opprK.
Qed.

Lemma sumbtv_out : [> '0 ; '0 <] + [> '1 ; '1 <] = \1.
Proof. by rewrite -[RHS](sumonb_out t2tv) big_bool addrC. Qed.

(* two qubit gate *)
Definition BMultiplexer (U V : 'End('Hs bool)) : 'End('Hs(bool * bool)%type):=
  [> '0 ; '0 <] ⊗f U + [> '1 ; '1 <] ⊗f V.
Lemma BMultiplexerE U V : 
  BMultiplexer U V = [> '0 ; '0 <] ⊗f U + [> '1 ; '1 <] ⊗f V.
Proof. by []. Qed. 
Lemma BMultiplexer_unitary (U V : 'FU('Hs bool)) :
  BMultiplexer U V \is unitarylf.
Proof.
apply/unitarylfP; rewrite /BMultiplexer raddfD/= !tentf_adj.
rewrite !adj_outp linearDl/= !linearDr/= !tentf_comp !outp_comp.
rewrite !onb_dot/= !scale0r !ten0tf !scale1r !unitaryf_form addr0 add0r.
by rewrite -linearDl/= sumbtv_out tentf11.
Qed.
HB.instance Definition _ (U V : 'FU('Hs bool)) :=
  isUnitaryLf.Build 'Hs(bool * bool)%type (BMultiplexer U V) (@BMultiplexer_unitary U V).

Lemma BMultiplexer_adj U V : (BMultiplexer U V)^A = BMultiplexer U^A V^A.
Proof. by rewrite /BMultiplexer raddfD/= !tentf_adj !adj_outp. Qed.

Lemma BMultiplexerE0 (U V : 'End('Hs bool)) (u : 'Hs bool) : 
  BMultiplexer U V ('0 ⊗t u) = '0 ⊗t (U u).
Proof.
by rewrite /BMultiplexer lfunE/= !tentf_apply 
  !outpE !onb_dot/= scale0r ten0tv addr0 scale1r.
Qed.

Lemma BMultiplexerE1 (U V : 'End('Hs bool)) (u : 'Hs bool) : 
  BMultiplexer U V ('1 ⊗t u) = '1 ⊗t (V u).
Proof.
by rewrite /BMultiplexer lfunE/= !tentf_apply 
  !outpE !onb_dot/= scale0r ten0tv add0r scale1r.
Qed.

Definition BControl (U : 'End('Hs bool)) := BMultiplexer \1 U.
Lemma BControlE U : BControl U = [> '0 ; '0 <] ⊗f \1 + [> '1 ; '1 <] ⊗f U.
Proof. by []. Qed.
Lemma BControlE0 (U : 'End('Hs bool)) (u : 'Hs bool) : 
  BControl U ('0 ⊗t u) = '0 ⊗t u.
Proof. by rewrite BMultiplexerE0 lfunE. Qed.
Lemma BControlE1 (U : 'End('Hs bool)) (u : 'Hs bool) : 
  BControl U ('1 ⊗t u) = '1 ⊗t (U u).
Proof. exact: BMultiplexerE1. Qed.

Lemma BControl_adj U : (BControl U)^A = BControl U^A.
Proof. by rewrite /BControl BMultiplexer_adj adjf1. Qed.

Definition CNOT := BControl ''X.
Lemma CNOTE : CNOT = [> '0 ; '0 <] ⊗f \1 + [> '1 ; '1 <] ⊗f ''X. 
Proof. by []. Qed.
Lemma CNOTE0 (u : 'Hs bool) : CNOT ('0 ⊗t u) = '0 ⊗t u. Proof. exact: BControlE0. Qed.
Lemma CNOTE1 (u : 'Hs bool) : CNOT ('1 ⊗t u) = '1 ⊗t (''X u). Proof. exact: BControlE1. Qed.
(* move *)
Lemma PauliX_cb b : PauliX ''b = ''(negb b).
Proof. by case: b; rude_bmx. Qed.
Lemma CNOT_cb b1 b2 : CNOT (''b1 ⊗t ''b2) = ''b1 ⊗t ''(b1 (+) b2).
Proof. by case: b1; rewrite ?CNOTE0 ?CNOTE1 ?PauliX_cb. Qed.

Definition CZGate := BControl ''Z.
Lemma CZGateE : CZGate = [> '0 ; '0 <] ⊗f \1 + [> '1 ; '1 <] ⊗f ''Z. 
Proof. by []. Qed.
Lemma CZGateE0 (u : 'Hs bool) : CZGate ('0 ⊗t u) = '0 ⊗t u. Proof. exact: BControlE0. Qed.
Lemma CZGateE1 (u : 'Hs bool) : CZGate ('1 ⊗t u) = '1 ⊗t (''Z u). Proof. exact: BControlE1. Qed.
(* move *)
Lemma PauliZ_cb b : PauliZ ''b = (-1)^b *: ''b.
Proof. by case: b; rude_bmx. Qed.
Lemma CZGate_cb b1 b2 : CZGate (''b1 ⊗t ''b2) = (''b1 ⊗t (-1)^(b1&&b2) *: ''b2).
Proof. by case: b1; rewrite ?CZGateE0 ?CZGateE1 ?PauliZ_cb//= expr0z scale1r. Qed.

(* Definition BSWAP : 'End('Hs (bool * bool)%type) := 
    @swaptf [ihbFinType of bool] [ihbFinType of bool].
Lemma BSWAP_unitary : BSWAP \is unitarylf.
Proof.
apply/unitarylfP; apply/intro_tv=>u v.
by rewrite /BSWAP swaptf_adj !lfunE/= !swaptfEtv.
Qed.
Canonical BSWAP_unitaryfType := UnitaryfType BSWAP_unitary.
Lemma BSWAPE (u v : 'Hs bool) : BSWAP (u ⊗t v) = v ⊗t u.
Proof. by rewrite swaptfEtv. Qed. *)

End BoolGates.

Notation "'''H'" := Hadamard.
Notation "'''X'" := PauliX.
Notation "'''Y'" := PauliY.
Notation "'''Z'" := PauliZ.
Notation "'''S'" := SGate.
Notation "''Rx' r" := (RxGate r) (at level 2, format "''Rx' r").
Notation "''Ry' r" := (RyGate r) (at level 2, format "''Ry' r").
Notation "''Rz' r" := (RzGate r) (at level 2, format "''Rz' r").
Notation "''0'" := (t2tv false) (at level 0).
Notation "''1'" := (t2tv true) (at level 0).
Notation "'''' t" := (t2tv t) (at level 2, format "'''' t").
Notation "''+'" := (pmbasis false) (at level 0).
Notation "''-'" := (pmbasis true) (at level 0).
Notation "''±' b" := (pmbasis b) (at level 2, format "''±' b").
Notation "''ph' r" := (phstate r) (at level 2, format "''ph'  r").
Notation "U '⊕' V" := (BMultiplexer U V) 
  (at level 50, V at next level, left associativity).
Notation "''CU' U" := (BControl U) (at level 2, format "''CU' U").
Notation "'''CZ'" := CZGate.
Notation "'SWAP'" := (@swaptf _ _).


Section PUnitary.
Variable (H : chsType) (F : finType) (f g : 'PONB(F;H)).

Lemma PUnitary_subproof : { U : 'FU(H) & forall i, U (f i) = g i}.
Proof.
pose U := \sum_i [> ponb_ext g i ; ponb_ext f i<].
have UU: U \is unitarylf.
apply/unitarylfP; rewrite /U linear_sumr/= -(sumonb_out (ponb_ext f)).
by apply eq_bigr=>i _; rewrite linear_sum linear_suml/= (bigD1 i)//= big1=>[j/negPf nj|];
rewrite adj_outp outp_comp onb_dot ?nj ?scale0r// eqxx scale1r addr0.
exists (UnitaryLf_Build UU)=>i/=.
rewrite /U sum_lfunE (bigD1 (inl i))//= big1=>[j/negPf nj|];
by rewrite outpE -!(ponb_extE f) onb_dot ?nj ?scale0r// eqxx scale1r addr0.
Qed.
Definition PUnitary := projT1 (PUnitary_subproof).
Lemma PUnitaryE i : PUnitary (f i) = g i.
Proof. by move: (projT2 (PUnitary_subproof)). Qed.
Lemma PUnitaryEV i : (PUnitary)^A (g i) = f i.
Proof. by rewrite -PUnitaryE -comp_lfunE unitaryf_form lfunE. Qed.
End PUnitary.

Section VUnitary.
Variable (H : chsType).

Definition ponb1_fun (u : H) := (fun i : 'I_1 => u).
Lemma ponb1_ponb (u : 'NS(H)) i j : [< ponb1_fun u i ; ponb1_fun u j >] = (i == j)%:R.
Proof. by rewrite /ponb1_fun ns_dot !ord1 eqxx. Qed.
HB.instance Definition _ (u : 'NS(H)) :=
  isPONB.Build H 'I_1 (ponb1_fun u) (@ponb1_ponb u).
Definition VUnitary (u v : 'NS(H)) := PUnitary (ponb1_fun u) (ponb1_fun v).
Lemma VUnitaryE (u v : 'NS(H)) : @VUnitary u v (u : H) = v :> H.
Proof. by move: (PUnitaryE (ponb1_fun u) (ponb1_fun v))=>/(_ ord0). Qed.
Lemma VUnitaryEV (u v : 'NS(H)) : (@VUnitary u v)^A (v : H) = u :> H.
Proof. by rewrite -(VUnitaryE u) -comp_lfunE unitaryf_form lfunE. Qed.
End VUnitary.

HB.lock
Definition uniformtv (T : ihbFinType) : 'Hs T := 
    ((sqrtC #|T|%:R)^-1) *: \sum_i ''i.
Canonical uniformtv_unlockable := Unlockable uniformtv.unlock.

HB.lock
Definition Multiplexer (T1 T2 : ihbFinType) :=
  fun f : T1 -> 'End('Hs T2) => 
  (\sum_i ([> ''i ; ''i <] ⊗f (f i))) : 'End('Hs (T1 * T2)%type).
Canonical Multiplexer_unlockable := Unlockable Multiplexer.unlock.

Section GeneralGates.
Implicit Type (T : ihbFinType).

Lemma uniformtvE T :
  uniformtv T = (((sqrtC #|T|%:R)^-1) *: \sum_i ''i).
Proof. by rewrite [uniformtv]unlock. Qed.
Lemma uniformtv_ns T : [< uniformtv T ; uniformtv T >] == 1%:R.
Proof.
apply/eqP; rewrite uniformtvE linearZl_LR linearZr/= linear_suml/=.
rewrite (eq_bigr (fun _=>1%:R))=>[i _|].
by rewrite linear_sum/= (bigD1 i)//= big1=>[j/negPf nj|];
   rewrite onb_dot ?eqxx ?addr0// eq_sym nj.
rewrite sumr_const cardE -cardT -mulr_natr mul1r mulrA ?divc_simp mulfV//.
by rewrite lt0r_neq0// ltr0n ihb_dim ihb_dim_proper.
Qed.
HB.instance Definition _ (T : ihbFinType) :=
  isNormalState.Build ('Hs T) (uniformtv T) (eqP (uniformtv_ns T)).
Global Arguments uniformtv {T}.

Lemma dotp_uniformtvcb T (i : T) : [< uniformtv ; ''i >] = (sqrtC #|T|%:R)^-1.
Proof.
rewrite uniformtvE linearZl_LR linear_suml/= (bigD1 i)//= big1=>[j/negPf nj|];
by rewrite onb_dot ?nj// eqxx addr0 mulr1 !divc_simp.
Qed.
Lemma uniformtv_bool : uniformtv = '+.
Proof.
rewrite uniformtvE card_bool [RHS](onb_vec (t2tv)).
by rewrite /= !big_bool !dotp_cbpm sign_simp scalerDr.
Qed.

Lemma MultiplexerE T1 T2 f : 
  @Multiplexer T1 T2 f = \sum_i ([> ''i ; ''i<] ⊗f (f i)).
Proof. by rewrite [Multiplexer]unlock. Qed. 
Lemma Multiplexer_unitary T1 T2 (f : T1 -> 'FU('Hs T2)) :
  Multiplexer f \is unitarylf.
Proof.
apply/unitarylfP; rewrite MultiplexerE -tentf11 -[in RHS](sumonb_out (t2tv)).
rewrite linear_sum/= !linear_suml/=; apply eq_bigr=>i _.
rewrite tentf_adj adj_outp linear_sumr/= (bigD1 i)//= big1=>[j/negPf nj|];
rewrite tentf_comp outp_comp onb_dot 1?eq_sym ?nj ?scale0r ?ten0tf//.
by rewrite eqxx scale1r unitaryf_form addr0.
Qed.
HB.instance Definition _ T1 T2 (f : T1 -> 'FU('Hs T2)) :=
  isUnitaryLf.Build 'Hs(T1 * T2)%type (Multiplexer f) (@Multiplexer_unitary T1 T2 f).

Lemma MultiplexerEt T1 T2 (f : T1 -> 'End('Hs T2)) (t : T1) (u : 'Hs T2) : 
  Multiplexer f (''t ⊗t u) = ''t ⊗t (f t u).
Proof.
by rewrite MultiplexerE sum_lfunE (bigD1 t)//= big1=>[i/negPf ni|];
rewrite tentf_apply outpE onb_dot ?ni ?scale0r ?ten0tv// eqxx scale1r addr0.
Qed.

Lemma Multiplexer_adj T1 T2 (f : T1 -> 'End('Hs T2)) :
  (Multiplexer f)^A = Multiplexer (fun i=>(f i)^A).
Proof.
by rewrite !MultiplexerE raddf_sum/=; 
under eq_bigr do rewrite tentf_adj adj_outp.
Qed.

Lemma MultiplexerEVt T1 T2 (f : T1 -> 'End('Hs T2)) (t : T1) (u : 'Hs T2) : 
  (Multiplexer f)^A (t2tv t ⊗t u) = t2tv t ⊗t ((f t)^A u).
Proof. by rewrite Multiplexer_adj MultiplexerEt. Qed.

Definition runity N n := expip (2%:R * n%:R / N%:R).
Lemma runityE N n : runity N n = expip (2%:R * n%:R / N%:R). Proof. by []. Qed.
End GeneralGates.

HB.lock
Definition QFTv n (t : 'I_n.+1) : 'Hs ('I_n.+1) := 
  ((sqrtC n.+1%:R)^-1) *: \sum_(i < n.+1) runity n.+1 (t * i)%N *: ''i.
Canonical QFTv_unlockable := Unlockable QFTv.unlock.
Global Arguments QFTv {n}.

HB.lock
Definition QFT n := \sum_i [>@QFTv n i ; ''i<].
Canonical QFT_unlockable := Unlockable QFT.unlock.
Global Arguments QFT {n}.

HB.lock
Definition PhOracle (T : ihbFinType) (f : T -> bool) : 'End('Hs T) :=
  \sum_(i : T) (-1) ^ (f i) *: [> ''i ; ''i <].
Canonical PhOracle_unlockable := Unlockable PhOracle.unlock.

HB.lock
Definition Oracle (T : ihbFinType) (W : finZmodType) (f : T -> W) : 'End('Hs (T * W)%type) :=
  \sum_(i : T)\sum_(j : W) [>t2tv i ⊗t t2tv (j + f i); t2tv i ⊗t t2tv j<].
Canonical Oracle_unlockable := Unlockable Oracle.unlock.

Section GeneralGates.
Implicit Type (T : ihbFinType).

Lemma QFTvE n t : @QFTv n t =
  ((sqrtC n.+1%:R)^-1) *: \sum_(i < n.+1) runity n.+1 (t * i)%N *: ''i.
Proof. by rewrite [@QFTv]unlock. Qed.
Lemma QFTv_onb n i j : [<@QFTv n i ; @QFTv n j >] = (i == j)%:R.
Proof.
rewrite !QFTvE linearZl_LR/= linearZr/= linear_suml/=.
rewrite (eq_bigr (fun i0 : 'I_n.+1=>expip (2%:R * (j%:R - i%:R) * i0%:R / n.+1%:R)))=>[k _|].
rewrite linear_sumr (bigD1 k)//= big1=>[l/negPf nl|];
by rewrite linearZl_LR/= linearZr/= onb_dot 1?eq_sym ?nl ?mulr0// eqxx mulr1 addr0 
  /runity -expipNC -expipD !natrM mulrBr !mulrBl addrC !mulrA.
rewrite expip_sum_ord// eq_sym; case: eqP=>_;
by rewrite ?mul0r ?mulr0// mul1r !divc_simp mulfV// pnatr_eq0.
Qed.
HB.instance Definition _ n :=
  isONB.Build 'Hs('I_n.+1) 'I_n.+1 (@QFTv n) (@QFTv_onb n) (ihb_dim _).
HB.instance Definition _ n i := 
  NormalState.copy (@QFTv n i) ((@QFTv n : 'PONB) i : 'NS).

Lemma dotp_cbQFT m i j : 
  [< ''i ; @QFTv m j >] = (sqrtC m.+1%:R)^-1 * runity m.+1 (j * i).
Proof.
rewrite QFTvE dotpZr dotp_sumr (bigD1 i)//= big1=>[k/negPf nk|];
by rewrite dotpZr ?ns_dot ?onb_dot 1?eq_sym ?nk ?mulr0// addr0 mulr1.
Qed.

Lemma QFTE n : @QFT n = \sum_i [> QFTv i ; ''i<].
Proof. by rewrite [@QFT]unlock. Qed.
Lemma QFT_unitary n : @QFT n \is unitarylf.
Proof.
apply/unitarylfP; rewrite QFTE -(sumonb_out t2tv) !linear_sum/= linear_suml/=.
apply eq_bigr=>i _; rewrite adj_outp linear_sumr/= (bigD1 i)//= big1=>[j/negPf nj|];
by rewrite outp_comp onb_dot 1?eq_sym ?nj ?scale0r// eqxx scale1r addr0.
Qed.
HB.instance Definition _ n :=
  isUnitaryLf.Build 'Hs('I_n.+1) (@QFT n) (@QFT_unitary n).
Lemma QFTEt n (i : 'I_n.+1) : QFT ''i = QFTv i.
Proof.
rewrite QFTE sum_lfunE (bigD1 i)//= big1=>[j/negPf nj|];
by rewrite outpE onb_dot ?nj ?scale0r// eqxx scale1r addr0.
Qed.

Definition IQFT n := (@QFT n)^A.
Global Arguments IQFT {n}.
Lemma IQFTE n : @IQFT n = QFT^A. Proof. by []. Qed.
Lemma IQFTEt n (i : 'I_n.+1) : IQFT (QFTv i) = ''i.
Proof. by rewrite IQFTE -QFTEt -comp_lfunE unitaryf_form lfunE. Qed.

Lemma PhOracleE T (f : T -> bool) : PhOracle f = 
  \sum_(i : T) (-1) ^ (f i) *: [> ''i ; ''i <].
Proof. by rewrite [PhOracle]unlock. Qed.
Lemma PhOracleEt T (f : T -> bool) t :
  PhOracle f ''t = (-1) ^ (f t) *: ''t.
Proof.
by rewrite PhOracleE sum_lfunE (bigD1 t)//= big1/==>[i/negPf ni|];
rewrite lfunE/= outpE onb_dot ?ni ?scale0r ?scaler0// eqxx scale1r addr0.
Qed.
Lemma PhOracle_adj T (f : T -> bool) : (PhOracle f)^A = PhOracle f.
Proof.
rewrite PhOracleE raddf_sum/=; apply eq_bigr=>i _.
by rewrite adjfZ adj_outp; f_equal; case: (f i); rewrite ?expr0z ?expr1z ?conjC1// conjCN1.
Qed.
Lemma PhOracleEVt T (f : T -> bool) t :
  (PhOracle f)^A ''t = (-1) ^ (f t) *: ''t.
Proof. by rewrite PhOracle_adj PhOracleEt. Qed.
Lemma PhOracle_unitary T (f : T -> bool) :
  PhOracle f \is unitarylf.
Proof.
apply/unitarylfP; apply/(intro_onb t2tv)=>i.
by rewrite/= !lfunE/= PhOracleEt linearZ/= PhOracleEVt linearZ/= scalerA -!exprnP 
  -expr2 exprAC expr2 mulrN1 opprK expr1n scale1r.
Qed.
HB.instance Definition _ T (f : T -> bool) :=
  isUnitaryLf.Build ('Hs T) (PhOracle f) (@PhOracle_unitary T f).

(* Definition SWAP T : 'End('Hs (T * T)) := @swaptf T T.
Arguments SWAP {T}.
Lemma SWAP_unitary T : @SWAP T \is unitarylf.
Proof.
apply/unitarylfP; apply/intro_tv=>u v.
by rewrite swaptf_adj !lfunE/= !swaptfEtv.
Qed.
Canonical SWAP_unitaryfType T := UnitaryfType (@SWAP_unitary T).
Lemma SWAPE T (u v : 'Hs T) : SWAP (u ⊗t v) = v ⊗t u.
Proof. by rewrite swaptfEtv. Qed.
Lemma SWAPb : SWAP = BSWAP. Proof. by []. Qed. *)

Section Oracle.
Implicit Type (W : finZmodType).

Lemma OracleE T W (f : T -> W) : Oracle f = 
  \sum_(i : T)\sum_(j : W) [>t2tv i ⊗t t2tv (j + f i); t2tv i ⊗t t2tv j<].
Proof. by rewrite [Oracle]unlock. Qed.
Lemma OracleEt T W (f : T -> W) t1 t2 :
  Oracle f (''t1 ⊗t ''t2) = ''t1 ⊗t ''(t2 + f t1).
Proof.
rewrite OracleE sum_lfunE (bigD1 t1)//= sum_lfunE (bigD1 t2)//= !big1/= 
  =>[i/negPf ni|i/negPf ni|]. 2: rewrite sum_lfunE big1//==>[j _].
all: rewrite outpE tentv_dot !onb_dot ?ni ?mulr0 ?mul0r ?scale0r//.
by rewrite !eqxx mul1r scale1r !addr0.
Qed.
Lemma OracleEVt T W (f : T -> W) t1 t2 :
  (Oracle f)^A (''t1 ⊗t ''t2) = ''t1 ⊗t ''(t2 - f t1).
Proof.
apply/(intro_onbl t2tv2_onbasis)=>[[i j]].
rewrite /=/tentv_fun/= adj_dotEr OracleEt !tentv_dot !onb_dot.
by case: eqP=>[->|_]; rewrite ?mul0r// !mul1r eq_sym -subr_eq eq_sym.
Qed.

Lemma Oracle_unitary T W (f : T -> W) :
  Oracle f \is unitarylf.
Proof.
apply/unitarylfP; apply/(intro_onb t2tv2_onbasis)=>[[i j]].
by rewrite /=/tentv_fun/= !lfunE/= OracleEt OracleEVt addrK.
Qed.
HB.instance Definition _ T W (f : T -> W) :=
  isUnitaryLf.Build 'Hs(T * W)%type (Oracle f) (@Oracle_unitary T W f).
End Oracle.

End GeneralGates.

Arguments QFT {n}.
Arguments IQFT {n}.


(* we may introduce a set of variables, then proving things will be           *)
(* much easier; direct proof suffers from cast problem, after intro           *)
(* vars, we can inject things in dirac, and no more cast                      *)
Section UniformState.

Lemma uniformtv2 (T1 T2 : ihbFinType) :
  @uniformtv T1 ⊗t @uniformtv T2 = uniformtv.
Proof.
rewrite !uniformtvE tentvZl tentvZr scalerA; f_equal.
by rewrite -invfM -sqrtCM// -natrM card_prod.
rewrite tentv_suml pair_bigV/=; apply eq_bigr=>i _.
rewrite tentv_sumr; apply eq_bigr=>j _; exact: tentv_t2tv.
Qed.

Lemma uniformtv_tuple (T : ihbFinType) n :
  tentv_tuple (fun i : 'I_n => (@uniformtv T)) = uniformtv.
Proof.
apply/(intro_onbl t2tv)=>i/=.
rewrite {1}t2tv_tuple tentv_tuple_dot -[in RHS]conj_dotp dotp_uniformtvcb.
under eq_bigr do rewrite -conj_dotp dotp_uniformtvcb.
rewrite -rmorph_prod prodr_const card_tuple.
by rewrite natrX sqrtCX_nat exprVn card_ord.
Qed.

Lemma uniformtv_dffun (F : finType) (TF : F -> ihbFinType)  :
  tentv_dffun (fun i : F => @uniformtv (TF i)) = uniformtv.
Proof.
apply/(intro_onbl t2tv)=>i/=.
rewrite {1}t2tv_dffun tentv_dffun_dot -[in RHS]conj_dotp dotp_uniformtvcb.
under eq_bigr do rewrite -conj_dotp dotp_uniformtvcb.
rewrite -rmorph_prod card_dep_ffun foldrE big_map big_enum; f_equal.
rewrite -invf_prod -sqrt_prod -?natr_prod =>[? _ //|]; do 3 f_equal.
Qed.

Lemma uniformtv_ffun (F : finType) (T : ihbFinType)  :
  tentv_ffun (fun i : F=>@uniformtv T) = uniformtv.
Proof. exact: uniformtv_dffun. Qed.

End UniformState.

Section UniformTransformation.
Variable (T : ihbFinType).

Definition uniformtf := VUnitary ''(witness T) uniformtv.
Lemma uniformtfE : uniformtf ''(witness T) = uniformtv.
Proof. by rewrite VUnitaryE. Qed.
Lemma uniformtfEV : uniformtf^A uniformtv = ''(witness T).
Proof. by rewrite VUnitaryEV. Qed.

End UniformTransformation.

Arguments uniformtf {T}.
Notation "''Hn'" := (@uniformtf _).

Fixpoint bitstr2rat_fun (s : seq bool) : R :=
    match s with
    | [::] => 0
    | x :: t => x%:R / 2%:R + (bitstr2rat_fun t) / 2%:R
    end.
HB.lock
Definition bitstr2rat := bitstr2rat_fun.
Canonical bitstr2rat_unlockable := Unlockable bitstr2rat.unlock.

Section QFTTupleBasis.

Lemma uniq_eqE (T : eqType) n (s : n.-tuple T) (i j : 'I_n) :
  uniq s -> (s~_i == s~_j) = (i == j).
Proof. 
by move=>us; rewrite (tnth_nth (s~_i)) 
  [s~_j](tnth_nth (s~_i)) nth_uniq// size_tuple.
Qed.

Lemma bitstr_cons x (s : seq bool) : 
  bitstr2rat (x :: s) = x%:R / 2%:R + (bitstr2rat s) / 2%:R .
Proof. by rewrite unlock. Qed.
Lemma bitstr_rcons x (s : seq bool) :
  bitstr2rat (rcons s x) = bitstr2rat s + x%:R / 2%:R ^+ (size s).+1.
Proof.
rewrite unlock; elim: s=>[|y r IH]/=; first by rewrite mul0r addr0 add0r expr1.
by rewrite IH mulrDl addrA -mulrA -invfM !exprSr.
Qed.

Fixpoint bseq2nat_tr (n : nat) (bs : seq bool) : nat :=
  match bs with
  | [::] => n
  | x :: t => bseq2nat_tr (2 * n + x) t
  end.
Definition bseq2nat (bs : seq bool) := (bseq2nat_tr 0%N bs).
Lemma bseq2nat_acc n (bs : seq bool) :
  (bseq2nat_tr n bs =  (expn 2 (size bs)) * n + bseq2nat_tr 0 bs)%N.
Proof.
elim: bs n=>[n|b bs IH n]; first by rewrite /= expn0 mul1n addn0.
by rewrite /= IH [in RHS]IH addnA muln0 add0n expnSr mulnDr mulnA.
Qed.
Lemma bseq2nat_cons b (bs : seq bool) :
  (bseq2nat (b :: bs) = (expn 2 (size bs)) * b + bseq2nat bs)%N.
Proof. by rewrite /bseq2nat/= bseq2nat_acc muln0 add0n. Qed.
Lemma bseq2nat_rcons b (bs : seq bool) :
  (bseq2nat (rcons bs b)) = (2 * (bseq2nat bs) + b)%N.
Proof.
elim: bs b=>[b|x bs IH b]; first by rewrite /bseq2nat.
by rewrite /= !bseq2nat_cons IH size_rcons expnS mulnDr mulnA addnA.
Qed.

Lemma bitstr2rat_nat (bs : seq bool) :
  bitstr2rat bs = (bseq2nat bs)%:R / 2%:R ^+ (size bs).
Proof.
elim: bs=>[|x bs IH]; first by rewrite unlock /bseq2nat/= mul0r.
rewrite bitstr_cons bseq2nat_cons IH/= natrD mulrDl exprSr invfM 2!mulrA.
do ? f_equal. by rewrite natrM natrX mulrAC mulfV ?mul1r// expf_neq0.
Qed.

Lemma bseq2nat_le (bs : seq bool) : 
  (bseq2nat bs < expn 2 (size bs))%N.
Proof.
elim: bs=>[|x bs IH]. by rewrite /bseq2nat/= expn0.
rewrite bseq2nat_cons/= expnS mul2n -addnn -addnS leq_add//.
by rewrite -[X in (_ <= X)%N]muln1 leq_mul// leq_b1.
Qed.

Fixpoint nat2bseq_tr (n m : nat) (bs: seq bool) :=
  match n with
  | O => bs
  | S n' => nat2bseq_tr n' (m %/ 2) (odd m :: bs)
  end.
Definition nat2bseq n m := nat2bseq_tr n m [::].
Lemma nat2bseq_acc n m bs : 
  nat2bseq_tr n m bs = (nat2bseq_tr n m [::]) ++ bs.
Proof. by elim: n m bs=>[//|n IH m bs]; rewrite /= IH [in RHS]IH -catA/=. Qed.
Lemma nat2bseqS n m : nat2bseq n.+1 m = odd (m %/ expn 2 n) :: nat2bseq n m.
Proof.
rewrite /nat2bseq/=; elim: n m=>[m|n IH m]; first by rewrite /= expn0 divn1.
by rewrite nat2bseq_acc/= [in RHS]nat2bseq_acc -cat_cons IH -divnMA expnS.
Qed.
Lemma nat2bseq_tupleP n m : size (nat2bseq n m) == n.
Proof. by apply/eqP; elim: n m=>[m//|n IH m]; rewrite nat2bseqS/= IH. Qed.
Canonical nat2bseq_tuple n m := Tuple (nat2bseq_tupleP n m).
Lemma bseq2nat_exc n m k : nat2bseq n (2 ^ n * m + k) = nat2bseq n k.
Proof.
elim: n m k=>[m k//|n IH m k].
have P: (0 < 2 ^ n)%N by rewrite expn_gt0.
by rewrite !nat2bseqS expnSr -mulnA IH divnD// mulKn// modnMr 
  add0n leqNgt ltn_mod P/= addn0 oddD mul2n odd_double/= .
Qed.

Lemma bseq2natK n (bs : n.-tuple bool) : nat2bseq n (bseq2nat bs) = bs.
Proof.
elim: n bs=>[bs|n IH bs].
by rewrite tuple0/= /nat2bseq/=.
case/tupleP: bs=>x bs.
rewrite bseq2nat_cons size_tuple nat2bseqS bseq2nat_exc IH/=.
f_equal. have P: (0 < 2 ^ n)%N by rewrite expn_gt0.
rewrite divnD// mulKn// divn_small.
by move: (bseq2nat_le bs); rewrite size_tuple.
rewrite modnMr add0n leqNgt ltn_mod P/= !addn0.
by case: x.
Qed.

Lemma ltn_dropl n m p : (n + m < p -> n < p)%N.
Proof. rewrite !ltnNge; apply/contraNN=>P; apply/(leq_trans P)/leq_addr. Qed.

Lemma nat2bseqK n m : (m < expn 2 n)%N -> bseq2nat (nat2bseq n m) = m.
Proof.
elim: n m=>[m|n IH m]. by case: m=>[|m]; rewrite expn0.
rewrite nat2bseqS bseq2nat_cons size_tuple {1 3 4}(divn_eq m (expn 2 n)).
have P: (0 < 2 ^ n)%N by rewrite expn_gt0.
rewrite mulnC bseq2nat_exc IH ?ltn_mod// =>/ltn_dropl.
rewrite expnSr ltn_mul2l P/=.
case: (m %/ 2 ^ n)%N=>//= q; case: q=>//=.
Qed.

Lemma bseq2ord_subproof n (s : n.-tuple bool) : (bseq2nat s < expn 2 n)%N.
Proof. by rewrite -{2}(size_tuple s); apply bseq2nat_le. Qed.
Definition bseq2ord n (s : n.-tuple bool) := Ordinal (bseq2ord_subproof s).
Definition ord2bseq n (m : 'I_(expn 2 n)) := [tuple of nat2bseq n m].
Lemma bseq2ordK n : cancel (@bseq2ord n) (@ord2bseq n).
Proof.
move=>s. rewrite /bseq2ord /ord2bseq/=. apply/val_inj=>/=. apply bseq2natK.
Qed.
Lemma ord2bseqK n : cancel (@ord2bseq n) (@bseq2ord n).
Proof.
move=>k. destruct k. apply/val_inj. rewrite /ord2bseq /bseq2ord/= nat2bseqK//.
Qed.
Lemma bseq2ord_inj n : injective (@bseq2ord n).
Proof. exact: (can_inj (@bseq2ordK n)). Qed.
Lemma ord2bseq_inj n : injective (@ord2bseq n).
Proof. exact: (can_inj (@ord2bseqK n)). Qed.

Lemma big_bseq (V : zmodType) n (F : n.-tuple bool -> V) : 
  \sum_(i : n.-tuple bool) F i 
  = \sum_(i < expn 2 n) F (ord2bseq i).
Proof.
apply: reindex; exists (@bseq2ord n)=>x _; [apply: ord2bseqK | apply: bseq2ordK].
Qed.

Lemma ltn_dropr n m p : (n < p -> n - m < p)%N.
Proof. apply/leq_ltn_trans/leq_subr. Qed.

End QFTTupleBasis.

HB.lock
Definition QFTbv n (bs : n.-tuple bool) : 'Hs (n.-tuple bool) :=
  (sqrtC 2%:R ^- n) *: \sum_(i : n.-tuple bool) 
    (expip (2%:R * (bseq2ord bs * bseq2ord i)%:R / 2%:R ^+ n) *: ''i).
Canonical QFTbv_unlockable := Unlockable QFTbv.unlock.

Section QFTTupleBasis.

Lemma QFTbvE n bs : @QFTbv n bs =  ((sqrtC 2%:R ^- n) *: \sum_(i : n.-tuple bool) 
  (expip (2%:R * (bseq2ord bs * bseq2ord i)%:R / 2%:R ^+ n) *: ''i)).
Proof. by rewrite [QFTbv]unlock. Qed.

Lemma QFTbv_onb n (bs1 bs2 : n.-tuple bool) : 
  [< QFTbv bs1 ; QFTbv bs2 >] = (bs1 == bs2)%:R.
Proof.
rewrite !QFTbvE dotpZl dotpZr mulrA geC0_conj -?invfM ?invr_ge0 ?exprn_ge0// 
  ?sqrtC_ge0// -exprMn -expr2 sqrtCK dotp_suml; under eq_bigr do rewrite dotp_sumr.
rewrite (eq_bigr (fun i : n.-tuple bool => 
  (expip ( 2%:R * ((bseq2ord bs2)%:R - (bseq2ord bs1)%:R) * (bseq2ord i)%:R / 2%:R ^+ n)))).
move=>i _; rewrite (bigD1 i)//= big1=>[j/negPf nj|];
by rewrite dotpZl dotpZr ?ns_dot ?onb_dot 1?eq_sym ?nj ?mulr0// addr0 mulr1 
  -expipNC -expipD addrC -mulrBl !natrM -mulrBr -mulrBl mulrA.
rewrite big_bseq eq_sym; under eq_bigr do rewrite ord2bseqK -natrX.
by rewrite expip_sum_ord// natrX mulrCA (inj_eq (@bseq2ord_inj _))
   mulVf ?mulr1// expf_neq0.
Qed.
HB.instance Definition _ n :=
  isONB.Build 'Hs(n.-tuple bool) (n.-tuple bool) (@QFTbv n) (@QFTbv_onb n) (@ihb_dim _).

Lemma QFTbv_uniform n : QFTbv (nseq_tuple n false) = uniformtv.
Proof.
rewrite QFTbvE uniformtvE; f_equal; last apply eq_bigr=>i _.
by rewrite card_tuple card_bool natrX sqrtCX_nat.
suff P: bseq2ord (nseq_tuple n false) = 0%N :> nat.
by rewrite natrM P mul0r mulr0 mul0r expip0 scale1r.
by clear i; elim: n=>[//|n]; rewrite/= bseq2nat_cons=>->; rewrite muln0 addn0.
Qed.

Lemma big_bseq_recr (V : zmodType) n (F : n.+1.-tuple bool -> V) : 
  \sum_(i : n.+1.-tuple bool) F i 
  = \sum_b \sum_(i : n.-tuple bool) F [tuple of rcons i b].
Proof.
rewrite pair_big/=. apply: reindex=>/=.
exists (fun s=> (tlast s, [tuple of tfirst s]))=>x _.
by destruct x; rewrite /tlast tnthN/=; f_equal; apply/val_inj=>/=; rewrite tfirst_rcons.
by rewrite /= -tupleN_eta.
Qed.

(* QFT state can be written as a tensor product states *)
Lemma QFTbvTE n (bs : n.-tuple bool) :
  QFTbv bs = tentv_tuple (fun i=> phstate (bitstr2rat (drop (n.-1 - i) bs))).
Proof.
apply/(intro_onbl (t2tv))=>i.
rewrite/= QFTbvE dotpZr dotp_sumr (bigD1 i)//= big1=>[j/negPf nj|];
rewrite dotpZr ?ns_dot ?onb_dot 1?eq_sym ?nj ?mulr0// mulr1 addr0.
rewrite t2tv_tuple tentv_tuple_dot. 
under eq_bigr do rewrite dotp_cbph.
rewrite big_split/= expip_prod prodr_const card_ord exprVn; f_equal.
elim: n bs i=>/=[bs i|n IH bs i].
by rewrite !tuple0/=/bseq2nat/= mulr0 big_ord0 mul0r.
case/tupleP: bs=>[sl sh]; case/tupleNP: i=>[bl bh].
have P (i : 'I_n) : drop (n - i) [tuple of sl :: sh] = drop (n.-1 - i) sh.
rewrite drop_cons. case: i. clear -n. case: n sh=>// n bh m Pm/=; rewrite -subnSK//.
rewrite big_ord_recr/=; under eq_bigr do rewrite tnthNS P.
rewrite expipD -IH tnthN subnn drop0 -!mulrA bseq2nat_rcons.
rewrite bitstr2rat_nat/= !size_tuple mulnDr natrD [_/_]mulrDl mulrDr expipD; f_equal.
2: by do 2 f_equal; rewrite mulrA -natrM mulnC.
rewrite natrM mulnC natrM -!mulrA exprS invfM [_ * (_^-1 / _)]mulrA mulfV// mul1r.
rewrite bseq2nat_cons size_tuple natrD [X in 2 * X]mulrDl mulrDr expipD !natrM natrX mulrA.
rewrite mulrACA [_ * sl%:R / _]mulrAC mulfV ?expf_neq0// mul1r -mulrA -!natrM.
by rewrite expip2n mul1r natrM !mulrA.
Qed.

End QFTTupleBasis.

HB.lock
Definition expmxip (U : chsType) (F : finType) (onb : 'ONB(F;U)) (d : F -> R) : R -> 'End(U) := 
  fun t => \sum_i expip (d i * t) *: [> onb i ; onb i <].
Canonical expmxip_unlockable := Unlockable expmxip.unlock.

Section expmxip.
Variable (U : chsType) (F : finType) (onb : 'ONB(F;U)) (d : F -> R).
Local Notation expmxip := (@expmxip U F onb d).
(* e ^ i * pi * A * t *)
Lemma expmxipE t : expmxip t = \sum_i expip (d i * t) *: [> onb i ; onb i <].
Proof. by rewrite unlock. Qed.
Lemma expmxip_unitary t : expmxip t \is unitarylf.
Proof. 
apply/unitarylfP; rewrite -(sumonb_out onb) expmxipE !linear_sumr/=.
apply eq_bigr=>i _. rewrite linear_sum/= linear_suml/= (bigD1 i)//= big1=>[j/negPf nj|];
rewrite adjfZ adj_outp -comp_lfunZl -comp_lfunZr outp_comp onb_dot ?nj ?scale0r ?scaler0//.
by rewrite eqxx scale1r addr0 scalerA -expipNC -expipD addNr expip0 scale1r.
Qed.
HB.instance Definition _ (t : R) :=
  isUnitaryLf.Build U (expmxip t) (@expmxip_unitary t).
Lemma expmxip_adj t : (expmxip t)^A = expmxip (-t).
Proof.
rewrite !expmxipE linear_sum/=; apply eq_bigr=>i _.
by rewrite adjfZ adj_outp -expipNC mulrN.
Qed.
Lemma expmxipEt t i : expmxip t (onb i) = expip (d i * t) *: onb i.
Proof. 
rewrite expmxipE sum_lfunE (bigD1 i)//= big1=>[j/negPf nj|];
by rewrite lfunE/= outpE onb_dot ?nj ?scale0r ?scaler0// eqxx scale1r addr0.
Qed.
End expmxip.

Section ExpUnitary.
Variable (V : chsType).

Lemma explf_unitary (U : 'FU(V)) n : U%:VF ^+ n \is unitarylf.
Proof.
elim: n=>[|n /unitarylfP IH]; first by rewrite expr0 is_unitarylf.
by apply/unitarylfP; rewrite exprS adjf_comp comp_lfunA comp_lfunACA unitaryf_form comp_lfun1r.
Qed.
HB.instance Definition _ (U : 'FU(V)) n :=
  isUnitaryLf.Build V (U%:VF ^+ n) (@explf_unitary U n).

Lemma explf_adj (U : 'End(V)) n : (U^+n)^A = U^A^+n.
Proof.
elim: n=>[|n IH]; first by rewrite !expr0 adjf1.
by rewrite exprS adjf_comp IH exprSr.
Qed.
End ExpUnitary.
