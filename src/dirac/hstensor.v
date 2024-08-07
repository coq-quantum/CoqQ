(* -------------------------------------------------------------------- *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.
From quantum.external Require Import spectral.
From mathcomp.analysis Require Import -(notations)forms.
From mathcomp.classical Require Import boolp.
From mathcomp.analysis Require Import reals.
(* From mathcomp.real_closed Require Import complex. *)
From quantum.external Require Import complex.
From mathcomp.real_closed Require Import mxtens.
Require Import EqdepFacts Eqdep_dec.
(* -------------------------------------------------------------------- *)

Require Import mcextra mcaextra notation hermitian prodvect tensor cpo mxpred extnum ctopology quantum.
From quantum.dirac Require Import setdec.
Import Order.TTheory GRing.Theory Num.Theory Num.Def MxLownerOrder.
Import VectorInternalTheory.

(*****************************************************************************)
(*                          Composite Quantum System                         *)
(* ------------------------------------------------------------------------- *)
(* Providing a large system with atomic systems indicated by L (label set)   *)
(*   and their state space H : L -> chsType, we define the state space of    *)
(*   any subsystem S ⊆ L, 'H_S := ⊗_{i in S} H i                            *)
(*   'H_set0 is isomorphic to C (complex number), enabling to view both      *)
(*   vectors and dual vectors as special linear functions                    *)
(* ------------------------------------------------------------------------- *)
(*        'H[H]_S , 'H_S      :=  state space of subsystem S                 *)
(*      'Idx[H]_S , 'Idx_S    :=  index of 'H_S.  deltav (i : 'Idx_S) froms  *)
(*                                an orthonormal basis of 'H_S               *)
(*    'F[H]_(S,T) , 'F_(S,T)  :=  'Hom('H_S, 'H_T)  i.e., the linear         *)
(*                                function mapping from subsystem S to T     *)
(*        'F[H]_S , 'F_S      :=  'End('H_S)                                 *)
(*        'FV[H]_S , 'FV_S    :=  'Hom('H_set0, 'H_S)  i.e., the embedding   *)
(*                                of vectors to the linear function          *)
(*      'FdV[H]_S , 'FdV_S    :=  'Hom('H_S, 'H_set0)  i.e., the embedding   *)
(*                                of dual vectors to the linear function     *)
(* ------------------------------------------------------------------------- *)
(* Define tensor of vector/linear functions/super-operators lying/acting     *)
(*   on different subsystems                                                 *)
(*                                                                           *)
(*      tenv  ⊗v  := tensor of two vectors, 'H_S -> 'H_T -> 'H_(S :|: T)    *)
(*    tenvm        := tensor of a family of vectors, i.e.,                   *)
(*                    let f : (forall i : F, 'H_(S i)),                      *)
(*                      tenvm f : 'H_(\bigcup_i S i)                         *)
(*  ten_lfun  \⊗  := tensor of two lfun, 'F_(S1,T1) -> 'F_(S2,T2)           *)
(*                                        -> 'F_(S1 :|: S2, T1 :|: T2)       *)
(*    tenfm        := tensor of a family of lfun, i.e.,                      *)
(*                    let f : (forall i : F, 'F_(S i, T i)),                 *)
(*                      tenfm f : 'F_(\bigcup_i S i, \bigcup_i T i)          *)
(*  dot_lfun  \·   := general composition of two lfun (via automatically     *)
(*                    lifting), i.e., f \· g = (f \⊗ \1) \o (g \⊗ \1) with *)
(*                    \1 over minimal subsystem that make it valid           *)
(* sdot_lfun  \O   := general composition of two endomorphism lfun,          *)
(*                    'F_S -> 'F_T -> 'F_(S :|: T)                           *)
(*     tenso  :⊗  := tensor of two super-operators, 'SO_(S1,T1)             *)
(*                    -> 'SO(S2,T2) -> 'SO(S1 :|: S2, T1 :|: T2)             *)
(* ------------------------------------------------------------------------- *)
(* Since above operations suffers type cast problem (we frequently change    *)
(*   the domain/codomain), we provide a light-weight mechanism to reasoning  *)
(*   about equivalence up to a type cast, to_Hnd and to_Fnd ltac.            *)
(* However, if too many type casts involved, we suggest to use non-dependent *)
(*   type formalization, i.e., the labelled Dirac notation                   *)
(* ------------------------------------------------------------------------- *)
(* cylindrical extension of 'F[H]_S, 'SO[H]_S                                *)
(*         lift_lf, liftso := lift to a larger space                         *)
(*       liftf_lf, liftfso := lift to the global space                       *)
(*****************************************************************************)

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

(* tensor.v *)

Local Open Scope ring_scope.
Local Open Scope lfun_scope.

Local Notation C := hermitian.C.

Reserved Notation "''H_' S"      (at level 8, S at level 2, format "''H_' S").
Reserved Notation "''H[' H ]_ S" (at level 8, S at level 2). (* only parsing *)
Reserved Notation "''Idx_' S"      (at level 8, S at level 2, format "''Idx_' S").
Reserved Notation "''Idx[' H ]_ S" (at level 8, S at level 2). (* only parsing *)
Reserved Notation "''F_' S"     (at level 8, S at level 2, format "''F_' S").
Reserved Notation "''FV_' S"    (at level 8, S at level 2, format "''FV_' S").
Reserved Notation "''FdV_' S"   (at level 8, S at level 2, format "''FdV_' S").
Reserved Notation "''F_' ( S )" (at level 8). (* only parsing *)
Reserved Notation "''F_' ( S , T )" (at level 8, format "''F_' ( S ,  T )").
Reserved Notation "''F[' H ]_ S"    (at level 8, S at level 2). (* only parsing *)
Reserved Notation "''FV[' H ]_ S"   (at level 8, S at level 2). (* only parsing *)
Reserved Notation "''FdV[' H ]_ S"  (at level 8, S at level 2). (* only parsing *)
Reserved Notation "''F[' H ]_ ( S )"     (at level 8). (* only parsing *)
Reserved Notation "''F[' H ]_ ( S , T )" (at level 8). (* only parsing *)

Section IdxDef.
Variable (I : finType) (E : I -> chsType).
Variable S : {set I}.
Local Notation Si := {i : I | i \in S }.

Variant idx : predArgType := 
  Idx of mvector (fun i : Si => 'I_(dim (E (val i)))).

Definition idx_val (i : idx) := let: Idx g := i in g.

HB.instance Definition _ := [isNew for idx_val].

Definition fun_of_idx u (i : Si) : 'I_(dim (E (val i))) := idx_val u i.

Coercion fun_of_idx : idx >-> Funclass.

HB.instance Definition _ := [Equality of idx by <:].
HB.instance Definition _ := [Choice of idx by <:].
HB.instance Definition _ := [Countable of idx by <:].
HB.instance Definition _ := [Finite of idx by <:].

End IdxDef.

HB.lock Definition idx_of_fun (I : finType) (E : I -> chsType) (S : {set I}) 
  (F : forall i : {i : I | i \in S }, 'I_(dim (E (val i)))) 
  := Idx (\mvector_ ( i : {i : I | i \in S }) F i).
Canonical idx_unlockable := Unlockable idx_of_fun.unlock.

Section IdxDef1.
Variable (I : finType) (E : I -> chsType) (S : {set I}).
Implicit Type (F : forall i : {i : I | i \in S }, 'I_(dim (E (val i)))).

Lemma idxE F i : idx_of_fun F i = F i.
Proof. by rewrite [in LHS]unlock /fun_of_idx/= mvE. Qed.

Lemma idxP (u v : idx E S) : (forall i, u i = v i) <-> u = v.
Proof.
rewrite /fun_of_idx; split=> [/= eq_uv | -> //].
by apply/val_inj/mvectorP=> i; apply: eq_uv.
Qed.

Lemma eq_idx F1 F2 : (forall i, F1 i = F2 i) ->
  idx_of_fun F1 = idx_of_fun F2.
Proof. by move=> eq_uv; apply/idxP => i; rewrite !idxE eq_uv. Qed.

End IdxDef1.

Notation "''Idx[' H ]_ S" := (@idx _ H S) (only parsing) : type_scope.
Notation "''Idx_' S" := 'Idx[_]_S : type_scope.
Notation "\idx[ H ]_ ( i : S ) E" := 
  ((idx_of_fun (fun i : {i : _ | i \in S } => E)) : @idx _ H S)
  (at level 36, E at level 36, i, S at level 50): ring_scope.

Lemma card_idx (I : finType) (E : I -> chsType) (S : {set I}) : 
  #|'Idx[E]_S| = (\prod_(i in S ) dim (E i))%N.
Proof.
rewrite card_sub card_mv card_dep_ffun foldrE big_image/= 
  (big_sig_set _ _ (fun i => #|'I_(dim (E i))|)%N);
by under eq_bigr do rewrite card_ord.
Qed.

Definition Hf (I : finType) (E : I -> chsType) (S : {set I}) := 
    (fun i : {i : I | i \in S } => E (val i)).
HB.lock
Definition Hs I E S  := tensor_chsType (@Hf I E S).
Lemma Hs_dim_cast {I E S} :
  dim (@Hs I E S) = dim (tensor_chsType (@Hf I E S)).
Proof. by rewrite Hs.unlock. Qed.
HB.lock
Definition n2i I E S (i : 'I_(dim (@Hs I E S))) : 'Idx[E]_S := 
    (Idx (n2i (cast_ord Hs_dim_cast i))).
HB.lock
Definition i2n I E S (i : 'Idx[E]_S) : 'I_(dim (@Hs I E S)) := 
    cast_ord (esym Hs_dim_cast) (i2n (idx_val i)).

Notation "''H[' H ]_ S" := (@Hs _ H S) (only parsing) : type_scope.
Notation "''H_' S" := 'H[_]_S : type_scope.
Notation "''F[' H ]_ ( S , T )" := ('Hom( @Hs _ H S, @Hs _ H T)) (only parsing): type_scope.
Notation "''FV[' H ]_ S" := 'F[H]_(set0, S) (only parsing) : type_scope.
Notation "''FdV[' H ]_ S" := 'F[H]_(S, set0) (only parsing) : type_scope.
Notation "''F[' H ]_ S" := 'F[H]_(S, S) (only parsing) : type_scope.
Notation "''F[' H ]_ ( S )" := 'F[H]_S (only parsing) : type_scope.
Notation "''F_' ( S , T )" := 'F[_]_(S, T) : type_scope.
Notation "''FV_' S" := 'F_(set0, S) : type_scope.
Notation "''FdV_' S" := 'F_(S, set0) : type_scope.
Notation "''F_' S" := 'F_(S, S) : type_scope.
Notation "''F_' ( S )" := 'F_S (only parsing) : type_scope.

HB.lock Definition deltav {I : finType} {E : I -> chsType} {S} 
  (i : 'Idx[E]_S) := eb (i2n i).
HB.lock Definition cdv {I : finType} {E : I -> chsType} {S} 
  (i : 'Idx[E]_S) (u: 'H_S) := [< deltav i; u >].

(* -------------------------------------------------------------------- *)
Section SetTensorSpace.
Context {I : finType} (E : I -> chsType).
Implicit Type (S T : {set I}).

Local Notation idx := (@idx I E).
Local Notation Hs := (@Hs I E).
Local Notation "'⊗' x" := (inject x) (at level 2, format "⊗ x").

Lemma n2iK {S} : cancel (@n2i I E S) (@i2n I E S).
Proof. by rewrite n2i.unlock i2n.unlock=>i; rewrite n2iK cast_ord_comp cast_ord_id. Qed.
Lemma i2nK {S} : cancel (@i2n I E S) (@n2i I E S).
Proof.
rewrite n2i.unlock i2n.unlock=>i; apply/val_inj.
by rewrite /= cast_ord_comp cast_ord_id i2nK.
Qed.
Lemma i2n_inj {S} : injective (@i2n I E S).
Proof. exact (can_inj i2nK). Qed.
Lemma n2i_inj {S} : injective (@n2i I E S).
Proof. exact (can_inj n2iK). Qed.

(* Lemma eb_mv S i : eb i = ⊗ (\mvector_(j : {i : I | i \in S }) eb ((@n2i I E S i) j)).
Proof. by []. Qed. *)

Lemma dv_dot S (i j : idx S) : [< deltav i ; deltav j >] = (i == j)%:R.
Proof. by rewrite deltav.unlock eb_dot (can_eq i2nK). Qed.

Lemma dv_norm S (i : idx S) : `|deltav i| = 1.
Proof. by rewrite hnormE dv_dot eqxx sqrtC1. Qed.

Lemma conj_dv S (i : idx S) : (deltav i)^*v = deltav i.
Proof. by rewrite deltav.unlock conjv_eb. Qed.

(* component on deltav i ; coordinate *)
Lemma cdvE S (i: idx S) (u: Hs S) : cdv i u = [< deltav i; u >].
Proof. by rewrite cdv.unlock. Qed.

Lemma cdv_is_linear S (i: idx S) : scalar (cdv i).
Proof. by move=>a u v; rewrite !cdvE linearP. Qed.
HB.instance Definition _ S i := GRing.isLinear.Build 
  C 'H_S C *%R (cdv i) (@cdv_is_linear S i).

Definition cdv_dv S (i j: idx S) : cdv i (deltav j) = (i == j)%:R.
Proof. by rewrite cdvE dv_dot. Qed.

Definition cdv_dvC S (i j: idx S) : cdv i (deltav j) = cdv j (deltav i).
Proof. by rewrite !cdv_dv eq_sym. Qed.

Lemma dec_dv S (u: Hs S) : u = \sum_i cdv i u *: deltav i.
Proof.
rewrite -intro_ebl=>i; rewrite dotp_sumr (bigD1 (n2i i))//= big1=>[j /negPf nji|].
by rewrite dotpZr deltav.unlock eb_dot eq_sym (can2_eq i2nK n2iK) nji mulr0.
by rewrite dotpZr cdvE deltav.unlock eb_dot n2iK eqxx mulr1 addr0.
Qed.

Lemma conj_cdv S (u: Hs S) i : cdv i u^*v = (cdv i u)^*.
Proof. by rewrite !cdvE conjv_dotr conj_dv conj_dotp. Qed.

Lemma adj_cdv S T (f: 'Hom(Hs S, Hs T)) i j : 
  cdv i (f^A (deltav j)) = (cdv j (f (deltav i)))^*.
Proof. by rewrite !cdvE adj_dotEr conj_dotp. Qed.

Lemma dot_cdv S (u v: Hs S) : [< u; v >] = \sum_i (cdv i u)^* * (cdv i v).
Proof. 
rewrite {1}(dec_dv u) {1}(dec_dv v).
rewrite dotp_suml; apply eq_bigr=> i _; rewrite dotp_sumr (bigD1 i) //= big1.
by move=>j /negPf nji; rewrite dotpZl dotpZr dv_dot eq_sym nji !mulr0.
by rewrite dotpZl dotpZr dv_dot eqxx mulr1 addr0.
Qed.

Lemma cdvP S (u v: Hs S) : 
  ((@cdv _ _ _)^~ u) =1 ((@cdv _ _ _)^~ v) <-> u = v.
Proof.
split; last by move=>->. move=> P; rewrite -intro_ebl => t.
by move: (P (n2i t)); rewrite !cdvE deltav.unlock !n2iK.
Qed.

Lemma intro_cdvl S (u v: Hs S) : 
  (forall i, cdv i u = cdv i v) <-> u = v.
Proof.
split; last by move=>->. move=> P; rewrite -intro_ebl => t.
by move: (P (n2i t)); rewrite !cdvE deltav.unlock !n2iK.
Qed.

Lemma intro_cdvr S (u v: Hs S) : 
  (forall i, [< u ; deltav i >] = [< v ; deltav i >]) <-> u = v.
Proof.
split; [| move=>-> //]; rewrite -intro_cdvl=> P t.
by apply (can_inj conjCK); rewrite !cdvE !conj_dotp.
Qed.

Lemma mv_dot S (x y: mvector (@Hf I E S)) :
  [< ⊗ x ; ⊗ y >] = \prod_i [< x i; y i>].
Proof. by rewrite -tdotpE. Qed.

Lemma dim_setten S : (dim (Hs S) = \prod_(i in S ) dim (E i))%N.
Proof. by rewrite Hs_dim_cast dim_tensor /Hf -big_sig_set. Qed.

(* Cast Index and State *)
Definition castidx S T (eqAB : S = T) (eA : idx S)  : idx T :=
  let: erefl in _ = T := eqAB return (idx T) in eA.

Lemma castidx_id S erefl_S (eA : idx S) : castidx erefl_S eA = eA.
Proof. by rewrite eq_axiomK. Qed.

Lemma castidx_comp S1 S2 S3 (eq_S1 : S1 = S2) (eq_S2 : S2 = S3) A :
  castidx eq_S2 (castidx eq_S1 A) = castidx (etrans eq_S1 eq_S2) A.
Proof. by case: S2 / eq_S1 eq_S2; case: S3 /. Qed.

Lemma castidxK S1 S2 (eq_S : S1 = S2) :
  cancel (castidx eq_S) (castidx (esym eq_S)).
Proof. by case: S2 / eq_S. Qed.

Lemma castidxKV S1 S2 (eq_S : S1 = S2) :
  cancel (castidx (esym eq_S)) (castidx eq_S).
Proof. by case: S2 / eq_S. Qed.

(* This can be use to reverse an equation that involves a cast. *)
Lemma castidx_sym S1 S2 (eq_S : S1 = S2) A1 A2 :
  A1 = castidx eq_S A2 -> A2 = castidx (esym eq_S) A1.
Proof. by move/(canLR (castidxK _)). Qed.

Definition casths S T (eqAB : S = T) (v : Hs S) : Hs T :=
  let: erefl in _ = T := eqAB return (Hs T) in v.

Lemma casths_id S erefl_S (v : Hs S) : casths erefl_S v = v.
Proof. by rewrite eq_axiomK. Qed.

Lemma casths_comp S1 S2 S3 (eq_S1 : S1 = S2) (eq_S2 : S2 = S3) v :
  casths eq_S2 (casths eq_S1 v) = casths (etrans eq_S1 eq_S2) v.
Proof. by case: S2 / eq_S1 eq_S2; case: S3 /. Qed.

Lemma casthsK S1 S2 (eq_S : S1 = S2) : 
  cancel (casths eq_S) (casths (esym eq_S)).
Proof. by case: S2 / eq_S. Qed.

Lemma casthsKV S1 S2 (eq_S : S1 = S2) : 
  cancel (casths (esym eq_S)) (casths eq_S).
Proof. by case: S2 / eq_S. Qed.

Lemma casths_sym S1 S2 (eq_S : S1 = S2) v1 v2 :
  v1 = casths eq_S v2 -> v2 = casths (esym eq_S) v1.
Proof. by move/(canLR (casthsK _)). Qed.

Lemma casths_is_linear S1 S2 (eq_S : S1 = S2) : 
  linear (casths eq_S).
Proof. by move=>a f g; case: S2 / eq_S; rewrite !casths_id. Qed.
HB.instance Definition _ S1 S2 (eq_S : S1 = S2) := 
  GRing.isLinear.Build C (Hs S1) (Hs S2) *:%R (casths eq_S) (casths_is_linear eq_S).

Lemma deltav_cast S S' (eqS : S = S') (i : idx S) :
    casths eqS (deltav i) = deltav (castidx eqS i).
Proof. by case: S' / eqS; rewrite !castidx_id. Qed.

Lemma cdv_cast S S' (eqS : S = S') (i : idx S) v :
    cdv (castidx eqS i) v = cdv i (casths (esym eqS) v).
Proof. by case: S' / eqS v=>v; rewrite !castidx_id. Qed.

Lemma cdv_castV S S' (eqS : S = S') (i : idx S') v :
    cdv i (casths eqS v) = cdv (castidx (esym eqS) i) v.
Proof. by case: S' / eqS i=>i; rewrite !castidx_id. Qed.

Lemma casths_dotl S S' (eqS : S = S') (u : Hs S) (v : Hs S') :
  [< casths eqS u ; v >] = [< u ; casths (esym eqS) v >].
Proof. by case: S' / eqS v; rewrite casths_id. Qed.

Lemma casths_dotr S S' (eqS : S' = S) (u : Hs S) (v : Hs S') :
  [< u ; casths eqS v >] = [< casths (esym eqS) u ; v >].
Proof. by case: S / eqS u; rewrite casths_id. Qed.

Lemma casths_dot S S' (eqS : S = S') u v:
  [< casths eqS u ; casths eqS v >] = [< u ; v >].
Proof. by case: S' / eqS; by rewrite !casths_id. Qed.

Definition castlf S T S' T' (eqST : (S = S') * (T = T')) (f : 'Hom(Hs S, Hs T)) : 
  'Hom(Hs S', Hs T') :=
  let: erefl in _ = T' := eqST.2 return 'Hom(Hs S', Hs T') in
    let: erefl in _ = S' := eqST.1 return 'Hom(Hs S', Hs T) in f.

Lemma castlf_id S T erefl_ST (f : 'Hom(Hs S, Hs T)) : castlf erefl_ST f = f.
Proof. by case: erefl_ST => e_S e_T; rewrite [e_S]eq_axiomK [e_T]eq_axiomK. Qed.

Lemma castlfE S T S' T' (eqS : (S = S')) (eqT : (T = T')) (f : 'Hom(Hs S, Hs T)) u :
  castlf (eqS, eqT) f u = casths eqT (f (casths (esym eqS) u)).
Proof.
by case: S' / eqS u; case: T' / eqT => u; rewrite castlf_id !casths_id. 
Qed.

Lemma castlf_comp S1 T1 S2 T2 S3 T3 (eq_S1 : S1 = S2) (eq_T1 : T1 = T2)
                                    (eq_S2 : S2 = S3) (eq_T2 : T2 = T3) f :
  castlf (eq_S2, eq_T2) (castlf (eq_S1, eq_T1) f)
    = castlf (etrans eq_S1 eq_S2, etrans eq_T1 eq_T2) f.
Proof.
by case: S2 / eq_S1 eq_S2; case: S3 /; case: T2 / eq_T1 eq_T2; case: T3 /.
Qed.

Lemma castlfK S1 T1 S2 T2 (eq_S : S1 = S2) (eq_T : T1 = T2) :
  cancel (castlf (eq_S, eq_T)) (castlf (esym eq_S, esym eq_T)).
Proof. by case: S2 / eq_S; case: T2 / eq_T. Qed.

Lemma castlfKV S1 T1 S2 T2 (eq_S : S1 = S2) (eq_T : T1 = T2) :
  cancel (castlf (esym eq_S, esym eq_T)) (castlf (eq_S, eq_T)).
Proof. by case: S2 / eq_S; case: T2 / eq_T. Qed.

(* This can be use to reverse an equation that involves a cast. *)
Lemma castlf_sym S1 T1 S2 T2 (eq_S : S1 = S2) (eq_T : T1 = T2) A1 A2 :
  A1 = castlf (eq_S, eq_T) A2 <-> A2 = castlf (esym eq_S, esym eq_T) A1.
Proof. by case: S2 / eq_S A1 A2; case: T2 / eq_T=>??; rewrite !castlf_id; split=>/esym. Qed.

Lemma castlf_is_linear S T S' T' (eqST : (S = S') * (T = T')) : 
  linear (castlf eqST).
Proof. 
move=>a f g; case: eqST => eqS eqT; case: S' / eqS; case: T' / eqT.
by rewrite !castlf_id.
Qed.
HB.instance Definition _  S T S' T' (eqST : (S = S') * (T = T')) := 
  GRing.isLinear.Build C 'Hom(Hs S, Hs T) 'Hom(Hs S', Hs T')
    *:%R (castlf eqST) (castlf_is_linear eqST).

Lemma castlf_complfl S T S' T' W (eqST: S = T') (eqTW : T = W) (f: 'Hom(Hs S, Hs T)) 
  (g: 'Hom(Hs S', Hs T')) :
  castlf (eqST, eqTW) f \o g = castlf (erefl, eqTW) (f \o castlf (erefl _, esym eqST) g).
Proof.
by move: f g; case: T' / eqST; case: W / eqTW => f g; rewrite !castlf_id.
Qed.

Lemma castlf_complfr S T S' T' W (eqST: T' = S) (eqSW : S' = W) (f: 'Hom(Hs S, Hs T)) 
  (g: 'Hom(Hs S', Hs T')) :
  f \o castlf (eqSW, eqST) g = castlf (eqSW, erefl) (castlf (esym eqST, erefl _) f \o g).
Proof.
by move: f g; case: S / eqST; case: W / eqSW => f g; rewrite !castlf_id.
Qed.

Lemma castlf_complf {S T S' T' W W'} (eqW : W = W') (eqS : S = S') (eqT : T = T')
  (f: 'Hom(Hs W, Hs T)) (g: 'Hom(Hs S, Hs W)) :
    castlf (eqS, eqT) (f \o g) = castlf (eqW, eqT) f \o castlf (eqS, eqW) g.
Proof. by case: W' / eqW; case: S' / eqS; case: T' / eqT; rewrite !castlf_id. Qed.

Lemma castlf_conj S T S' T' (eqST : (S = S') * (T = T')) (f: 'Hom(Hs S, Hs T)) : 
  (castlf eqST f)^C = castlf eqST f^C.
Proof.
by do [case: eqST; case: S' /; case: T' /] in f *; rewrite !castlf_id.
Qed.

Lemma castlf_adj S T S' T' (eqS : S = S') (eqT : T = T') (f: 'Hom(Hs S, Hs T)) : 
  (castlf (eqS, eqT) f)^A = castlf (eqT, eqS) f^A.
Proof. by case: S' / eqS; case: T' / eqT; rewrite !castlf_id. Qed.

Lemma castlf_tr S T S' T' (eqS : S = S') (eqT : T = T') (f: 'Hom(Hs S, Hs T)) : 
  (castlf (eqS, eqT) f)^T = castlf (eqT, eqS) f^T.
Proof. by case: S' / eqS; case: T' / eqT; rewrite !castlf_id. Qed.

Lemma castlf_outp S S' T T' (eqS : S = S') (eqT : T = T') (v : Hs S) (u : Hs T) :
  castlf (eqS, eqT) [> u ; v <] = [>casths eqT u ; casths eqS v <].
Proof. by case: S' / eqS u; case: T' / eqT => u; rewrite castlf_id !casths_id. Qed. 

Lemma castlf1 S T (eqST : (S = T)) :  (castlf (eqST,eqST) (\1 : 'End(Hs S))) = \1.
Proof. by case: T / eqST; rewrite castlf_id. Qed.

(* conjV with conjv of each atomic space *)
(* Lemma conj_mv S (x : mvector (@Hf I E S)) :
  (⊗ x)^*v = ⊗ (\mvector_(i:{i : I | i \in S}) ((x i)^*v)%VF).
Proof.
apply/intro_cdvl=>i; rewrite !cdvE conjv_dotr conj_dv deltav.unlock eb_mv !mv_dot.
by apply eq_bigr=>j _; rewrite !mvE i2nK conjv_dotr conjv_eb.
Qed. *)

Lemma lfunPD S T (f g : 'Hom(Hs S, Hs T)) : 
  (forall i, f (deltav i) = g (deltav i)) <-> f = g.
Proof.
split=> [P |-> //]; apply/lfunP=> u; rewrite (dec_dv u) !linear_sum /=.
by apply eq_bigr=> i _; rewrite !linearZ /= (P i).
Qed.

End SetTensorSpace.

Lemma map_cover (I J : finType) (fs: J -> {set I}) (s : J) : 
  fs s :<=: \bigcup_i (fs i).
Proof. by apply bigcup_sup. Qed.

Definition incl (I: finType) (A B: {set I}) (AsubB : A :<=: B) (a : {i | i \in A}) 
  : {i : I | i \in B} := exist _ (val a) (subsetP AsubB (val a) (projT2 a)).

Definition flatidx (I: finType) (E : I -> chsType) (J : finType) (fs: J -> {set I})
  (i: 'Idx[E]_(\bigcup_i (fs i))) : {dffun forall i : J, 'Idx[E]_(fs i)} 
  := [ffun s : J => \idx[E]_(j : fs s) i (incl (map_cover fs s) j)]. 

HB.lock Definition injectv (I: finType) (E : I -> chsType) (J : finType) (fs: J -> {set I}) 
  (x: mvector (fun i: J => 'H[E]_(fs i))) : 'H[E]_(\bigcup_i (fs i))
  := \sum_(e : 'Idx[E]_(\bigcup_i (fs i))) (\prod_i cdv (flatidx e i) (x i) *: deltav e).

Definition applyf (I : finType) (E : I -> chsType) (J: finType) (fs fs': J -> {set I}) 
  (f : mvector (fun i : J => 'F[E]_((fs i), (fs' i)))) (x : mvector (fun i : J => 'H[E]_(fs i))) :=
  \mvector_(i : J) f i (x i).

Definition injectf_r (I : finType) (E : I -> chsType) (J: finType) 
  (fs fs': J -> {set I}) (f : mvector (fun i : J => 'F[E]_((fs i), (fs' i))))
  (x : 'H[E]_(\bigcup_i (fs i))) (b : 'Idx[E]_(\bigcup_i (fs i))) :=
    (cdv b x) *: injectv (applyf f (\mvector_(i : J) deltav (flatidx b i))).

HB.lock Definition injectf_fun (I : finType) (E : I -> chsType) (J: finType) 
  (fs fs': J -> {set I}) (f : mvector (fun i : J => 'F[E]_((fs i), (fs' i))))
  (x : 'H[E]_(\bigcup_i (fs i))) : 'H[E]_(\bigcup_i (fs' i)) :=
  \sum_(b : 'Idx[E]_(\bigcup_i (fs i))) injectf_r f x b.

(* tensor product of set, for define \tenor_(i : J) E i later *)
Section SetTensorVect.
Context {I : finType} (E : I -> chsType).
Variables (J : finType) (fs: J -> {set I}).

(* a finType index J *)
(* fs : map each index : J to a {set I} *)
(* the tensor product of index J *)

(* Definition mapf : {set {set I}} := [set fs i | i : J]. *)
Notation bdom := (\bigcup_i (fs i)).
Notation flatidx := (@flatidx I E J fs).
Notation injectv := (@injectv I E J fs).

Definition disf := forall i j, i != j -> [disjoint fs i & fs j].

Definition setsub (A: {set I}) (a : I) (sub: a \in A) : {i | i \in A} 
  := exist _ a sub.

Lemma preidx_ex (x : {i | i \in bdom}) : {i | val x \in fs i}.
Proof. destruct x=>/=; move: i=>/bigcupP/sig2W [j Pj inj]; by exists j. Qed.

Definition preidx (j : {i | i \in bdom}) : J := projT1 (preidx_ex j).

Lemma preidxP (j : {i | i \in bdom}) : val j \in fs (preidx j).
Proof. by move: (projT2 (preidx_ex j)). Qed.

Lemma preidxU (i : J) (j : {k | k \in fs i}) : disf -> 
  (preidx (incl (map_cover fs i) j)) = i.
Proof.
rewrite /disf=>dis; set k:= (incl (map_cover fs i) j).
have Q: val k = val j. by [].
symmetry; apply/eqP; move: (preidxP k); apply/contraTT.
set m:= preidx k; rewrite Q=>P1.
move: (@dis _ _ P1). rewrite disjoint_subset=>/subsetP P2.
by apply: (P2 (val j)); destruct j.
Qed.

Definition packidx (f: {dffun forall i: J, 'Idx[E]_(fs i)}) : 'Idx[E]_bdom
  := \idx[E]_(j : bdom) f (preidx j) (setsub (preidxP j)).

Lemma packidxE (f : {dffun forall i : J, 'Idx[E]_(fs i)}) : disf -> 
  forall (i : J) (j: {k | k \in fs i}), packidx f (incl (map_cover fs i) j) = f i j.
Proof.
move=>dis i j; rewrite idxE. 
move: (preidxU j dis) (preidxP (incl (map_cover fs i) j)) => P.
rewrite P /=; destruct j => /= Q.
by rewrite (eq_irrelevance Q i0).
Qed.

Lemma flatidxE (eAB : 'Idx[E]_bdom) (i : {i | i \in bdom}) : 
  eAB i = flatidx eAB (preidx i) (setsub (preidxP i)).
Proof.
destruct i; rewrite ffunE idxE/= /incl.
congr (eAB (exist _ _ _)); by apply eq_irrelevance.
Qed.

Lemma flatidxK : cancel flatidx packidx.
Proof. by move=>e; apply/idxP=>j; rewrite idxE flatidxE. Qed.

Lemma packidxK : disf -> cancel packidx flatidx.
Proof. 
by move=>dis e; apply/ffunP=>j; rewrite ffunE; 
  apply/idxP=>k; rewrite idxE packidxE.
Qed.

Lemma flatidx_inj : injective flatidx.
Proof. exact: (can_inj flatidxK). Qed.

Lemma packidx_inj : disf -> injective packidx.
Proof. move=>dis; exact: (can_inj (packidxK dis)). Qed.

Lemma deltavm (b : 'Idx[E]_bdom) :
  deltav b = injectv (\mvector_(i : J) deltav (flatidx b i)).
Proof.
rewrite injectv.unlock (bigD1 b)//=.
rewrite (eq_bigr (fun=>1)).
by move=>i _; rewrite mvE cdv_dv eqxx.
rewrite prodr_const expr1n scale1r [X in _ + X]big1 ?addr0// =>i.
rewrite -(inj_eq flatidx_inj)=>/dffun_neqP[j/negPf nj].
pose fk k := ((flatidx i k) == (flatidx b k))%:R : C.
rewrite (eq_bigr fk)=>[k _|]; first by rewrite mvE cdv_dv.
suff ->: \prod_(i : J) fk i = 0 by rewrite scale0r.
by rewrite (bigD1 j)//= /fk nj mul0r.
Qed.

Lemma big_distr_idx (R: ringType) (F : forall j, 'Idx[E]_(fs j) -> R) : disf -> 
  \prod_(i : J) (\sum_(j : 'Idx[E]_(fs i)) F i j) =
  \sum_(k : 'Idx[E]_bdom) \prod_(i : J) F i (flatidx k i).
Proof.
move=> dis; rewrite big_distr_dffun (reindex (fun x : 'Idx[E]_bdom => 
  ([ffun i: J => flatidx x i] : {dffun forall i: J, 'Idx[E]_(fs i)}))).
exists (fun x => packidx x) => -[]; [move=> d _ |move=>f _].
by apply flatidx_inj => //; rewrite packidxK //; apply/ffunP=> i; rewrite ffunE.
by rewrite packidxK //; apply/ffunP=> i; rewrite ffunE.
by rewrite /=; apply eq_bigr=>k _; apply eq_bigr=>i _; rewrite ffunE.
Qed.

Lemma injectv_dot (x y : mvector (fun i : J => 'H[E]_(fs i))) : 
  disf -> hdotp x y = [< injectv x ; injectv y >].
Proof.
move=> dis; rewrite /hdotp !injectv.unlock dotp_suml.
rewrite (eq_bigr (fun v=> [< \prod_i cdv (flatidx v i) (x i) *: deltav v; 
          \prod_i cdv (flatidx v i) (y i) *: deltav v >])).
move=>v _; rewrite dotp_sumr (bigD1 v) //=.
rewrite -[RHS]addr0; congr (_ + _); rewrite big1 // => i /negPf niv. 
by rewrite dotpZl dotpZr dv_dot eq_sym niv !mulr0.
rewrite (eq_bigr (fun i=> \sum_j (cdv j (x i))^* * (cdv j (y i)))).
by move=>i _; rewrite dot_cdv.
rewrite [\sum_ _ _](eq_bigr (fun i=> \prod_i0 
    ((cdv (flatidx i i0) (x i0))^* * cdv (flatidx i i0) (y i0)))).
by move=>i _; rewrite dotpZl dotpZr dv_dot eqxx mulr1 rmorph_prod big_split.
by rewrite big_distr_idx.
Qed.

Lemma injectvZi (i : J) (a : C) (x : mvector (fun i : J => 'H[E]_(fs i))) : 
  injectv (a *:_i x) = a *: injectv x.
Proof.
rewrite !injectv.unlock scaler_sumr; apply eq_bigr=>e _; rewrite scalerA.
congr (_ *: _); rewrite !(bigD1 i (P := predT)) //= mulrA.
congr (_ * _); first by rewrite mvE eqxx linearZ.
by apply: eq_bigr=> j ne_ji; rewrite mvE eq_sym (negbTE ne_ji) scale1r.
Qed.

Lemma injectvDi (i: J) (x: mvector (fun i : J => 'H[E]_(fs i))) (v: 'H[E]_(fs i)) :
  injectv (x +_i v) = injectv x + injectv (x[<i ← v>]).
Proof.
rewrite !injectv.unlock -big_split /=; apply eq_bigr=>e _. rewrite -scalerDl.
congr (_ *: _); rewrite !(bigD1 i (P := predT)) //=.
rewrite !(msetii, mvE) linearD /= mulrDl; congr (_ * _ + _ * _);
 by apply/eq_bigr=> j ne_ji; rewrite !(mset_ne, mvE) 1?eq_sym // addr0.
Qed.

Lemma injectv_mlinear : mlinear injectv.
Proof.
move=> i a x v /=; rewrite injectvDi injectvZi; congr (_ + injectv _).
by apply/mvectorP=> j; rewrite !mvE; case: eqP => //; rewrite scale1r.
Qed.

Lemma injectv_eq0 (x : mvector (fun i : J => 'H[E]_(fs i))) :
  (exists i, x i = 0) -> (injectv x = 0).
Proof. by apply/mlinear0/injectv_mlinear. Qed.

Lemma injectv_eq0P (x : mvector (fun i : J => 'H[E]_(fs i))) :
  disf -> reflect (exists i, x i = 0) (injectv x == 0).
Proof. 
move=>dis; apply: (iffP eqP) => eq0; last first.
- by apply: mlinear0 => //; apply/injectv_mlinear.
apply/'exists_eqP; apply/contra_eqT: eq0 => eq0.
have {}eq0: forall i, exists j, cdv j (x i) != 0.
- move=> i; apply/existsP; rewrite -negb_forall.
  apply/contra: eq0 => /forallP /= eq0; apply/existsP.
  exists i. apply/eqP. rewrite -intro_cdvl => j.
  by rewrite linear0; apply/eqP.
pose e := [ffun i : J => xchoose (eq0 i)].
rewrite injectv.unlock; apply/eqP=>/cdvP /(_ (packidx e)) => /eqP; apply/negP.
rewrite linear0 linear_sum (bigD1 (packidx e)) //= [\sum_( _ | _) _]big1.
by move=>j /negPf nje; rewrite linearZ /= cdv_dv eq_sym nje mulr0.
rewrite linearZ /= cdv_dv eqxx packidxK // addr0 mulr1.
by apply/prodf_neq0 => i _; rewrite ffunE; apply/(xchooseP (eq0 i)).
Qed.

End SetTensorVect.

(* tensor product of linear functions *)
Section SetTensorLfun.
Context {I : finType} (E : I -> chsType).

(* fs : J -> {set I}, for domain of each component *)
(* fs' : J -> {set I}, for codomain of each component *)
(* f (j : J) : the linear functions of each component, Hs (fs j) -> Hs (fs' j) *)
Variables (J: finType) (fs fs': J -> {set I}).
Implicit Type (f : mvector (fun i : J => 'F[E]_((fs i), (fs' i)))).

Notation bdom := (\bigcup_i (fs i)).
Notation bcdom := (\bigcup_i (fs' i)).

Lemma injectf_fun_is_linear f : linear (injectf_fun f).
Proof.
move=>a u v; rewrite injectf_fun.unlock scaler_sumr -big_split /=.
by apply eq_bigr=>i _; rewrite /injectf_r linearP scalerDl scalerA.
Qed.
HB.instance Definition _ f := GRing.isLinear.Build C 'H[E]_bdom 'H[E]_bcdom
  *:%R (injectf_fun f) (injectf_fun_is_linear f).
Definition injectf f := linfun (injectf_fun f).

(* if domains are well-defined, i.e., pairwise disjoint *)
Lemma injectfE f : disf fs ->  forall x, injectf f (injectv x) = injectv (applyf f x).
Proof.
move=>dis x; rewrite lfunE/= injectf_fun.unlock /injectf_r /applyf !injectv.unlock.
rewrite (eq_bigr (fun b=> \sum_e (\prod_i (cdv (flatidx b i) (x i) *
     cdv (flatidx e i) (f i ((deltav (flatidx b i)))))) *:  deltav e)).
move=>i _; rewrite scaler_sumr; apply eq_bigr=> e _.
rewrite scalerA; congr (_ *: _).
rewrite linear_sum /= (bigD1 i) //= [\sum_( _ | _) _]big1.
by move=>j /negPf nji; rewrite linearZ /= cdv_dv eq_sym nji mulr0.
rewrite addr0 linearZ /= cdv_dv eqxx mulr1 -big_split /=.
by apply eq_bigr=> j _; rewrite !mvE.
rewrite exchange_big /=; apply eq_bigr=> e _; rewrite -scaler_suml; congr (_ *: _).
rewrite [RHS](eq_bigr (fun i=> \sum_j cdv j (x i) * cdv (flatidx e i) (f i (deltav j)))).
move=>i _; rewrite mvE {1}(dec_dv (x i)) !linear_sum; apply eq_bigr=> j _.
by rewrite !linearZ. by rewrite big_distr_idx.
Qed.

Lemma injectf_delta f b : injectf f (deltav b) = 
  injectv (applyf f (\mvector_(i : J) deltav (flatidx b i))).
Proof.
rewrite lfunE/= injectf_fun.unlock (bigD1 b)//= /injectf_r cdv_dv eqxx scale1r.
rewrite (eq_bigr (fun=>0)) => [j/negPf nj|].
by rewrite cdv_dv nj scale0r.
by rewrite sumr_const mul0rn addr0.
Qed.

Lemma injectfZi (i : J) (a : C) f : 
  injectf (a *:_i f) = a *: injectf f.
Proof.
apply/lfunPD=> j; rewrite injectf_delta lfunE/= injectf_delta /applyf.
rewrite -(injectvZi i); f_equal; apply/mvectorP=>k.
by rewrite !mvE lfunE/=.
Qed.

Lemma injectfDi (i: J) f (v: 'F[E]_(fs i, fs' i)) :
  injectf (f +_i v) = injectf f + injectf (f[<i ← v>]).
Proof.
apply/lfunPD=> j; rewrite injectf_delta lfunE/= !injectf_delta /applyf.
have ->: (\mvector_ (i0 : J) 
          f[<i ← v>] i0 ((\mvector_ (i1 : J) deltav (flatidx j i1)) i0)) =
  (\mvector_ (i0 : J) f i0 ((\mvector_ (i1 : J) deltav (flatidx j i1)) i0))
    [<i ← v (deltav (flatidx j i))>].
  apply/mvectorP=>k; rewrite !mvE; case: eqP=>[Pv | //].
  by case: k / Pv.
rewrite -injectvDi; f_equal; apply/mvectorP=>k.
rewrite !mvE. case: eqP=>[Pv | ]; last by rewrite !addr0.
by case: k / Pv; rewrite lfunE/=.
Qed.

Lemma injectf_mlinear : mlinear injectf.
Proof.
move=> i a x v /=; rewrite injectfDi injectfZi; congr (_ + injectf _).
by apply/mvectorP=> j; rewrite !mvE; case: eqP => //; rewrite scale1r.
Qed.

End SetTensorLfun.

(*********************************************************************)
(********************** lfundef.v ****************************)

HB.lock Definition idx_default {I : finType} {E : I -> chsType}
  {A : {set I}} : 'Idx[E]_A := n2i (cast_ord (dim_proper_cast) ord0).

Definition idx0 {I : finType} {E : I -> chsType} := @idx_default I E set0.

Section SetIndex.
Context {I : finType} {E : I -> chsType}.

Local Notation idx := (@idx _ E).
Implicit Type (A B C: {set I}).

Lemma dim_set0 : (dim ('H[E]_set0) = 1)%N.
Proof. by rewrite dim_setten big_set0. Qed.

Lemma eq_nset0 : forall x y: 'I_(dim ('H[E]_set0)), x = y.
Proof. by rewrite dim_set0 => x y; rewrite !ord1. Qed.

Lemma idx0E : all_equal_to (@idx0 I E).
Proof. by move=>x/=; apply/i2n_inj; apply/eq_nset0. Qed. 

Lemma subInR A B (i : {i|i \in (A :|: B)}) (NinL : (val i \in A) <> true) : val i \in B.
Proof. move/negP: NinL; destruct i => /=; by move/setUP: i => [-> |->]. Qed.

Lemma subInL A B (i : {i|i \in (A :|: B)}) (NinR : (val i \in B) <> true) : val i \in A. 
Proof. by move/negP: NinR; destruct i => /=; move/setUP: i => [-> |->]. Qed.

Definition idxU A B (eA : idx A) (eB : idx B) : 
  idx (A :|: B) := \idx[E]_ (i : (A :|: B)) ( 
  match val i \in A =P true with
  | ReflectT E => eA (setsub E)
  | ReflectF E => eB (setsub (subInR E))
  end).
  
Lemma idxUEl A B (eA : idx A) (eB : idx B) (dis: [disjoint A & B]) 
  (i : {i|i \in A})  : (idxU eA eB) (incl (subsetUl A B) i) = eA i.
Proof. by rewrite idxE; case: eqP=>p; destruct i=>//=;rewrite (eq_irrelevance i p). Qed.

Lemma idxUEr A B (eA : idx A) (eB : idx B) (dis: [disjoint A & B]) 
  (i : {i|i \in B})  : (idxU eA eB) (incl (subsetUr A B) i) = eB i.
Proof.
rewrite idxE; case: eqP; destruct i => /= p.
by move/disjointP: dis => disp; move: (disp _ p); rewrite i.
rewrite /setsub; suff E1: val (incl (subsetUr A B) (setsub i)) \in B.
by rewrite (eq_irrelevance (subInR _) E1) (eq_irrelevance i E1).
by move/negP: p => /=; apply contraTT; rewrite i.
Qed.

Definition idxSl A B (eAB : idx (A :|: B)) : idx A :=
  \idx[E]_ (i : A) eAB (incl (subsetUl A B) i).

Definition idxSr A B (eAB : idx (A :|: B)) : idx B :=
  \idx[E]_ (i : B) eAB (incl (subsetUr A B) i).

Lemma idxSE A B (eAB : idx (A :|: B)) (i : {i|i \in (A :|: B)}) 
  (dis: [disjoint A & B]) :
  eAB i = match val i \in A =P true with
  | ReflectT E => idxSl eAB (setsub E)
  | ReflectF E => idxSr eAB (setsub (subInR E))
  end.
Proof.
case: eqP => p; rewrite idxE /incl/=;
by destruct i; rewrite (eq_irrelevance (subsetP _ _ _) i).
Qed.

Lemma idxUS A B (eAB : idx (A :|: B)) : idxU (idxSl eAB) (idxSr eAB) = eAB.
Proof.
apply/idxP => i; rewrite idxE; case: eqP=>P1;
rewrite idxE; case: i P1=>i P P1;
by rewrite /incl/= (eq_irrelevance (subsetP _ _ _) P).
Qed.

Lemma idxSUl A B (eA : idx A) (eB : idx B) : idxSl (idxU eA eB) = eA.
Proof.
apply/idxP => i; rewrite !idxE.
case: eqP=>/=; case: i=>i/= P1 P2.
by rewrite /setsub (eq_irrelevance P1 P2).
by move: {+}P2; rewrite P1 in P2.
Qed.

Lemma idxSUr A B (dis: [disjoint A & B]) :
  forall (eA : idx A) (eB : idx B), idxSr (idxU eA eB) = eB.
Proof. by move=> eA eB; apply/idxP => i; rewrite idxE idxUEr. Qed.

Lemma idxBE A B (i j: idx (A :|: B)) :
  (idxSl i == (idxSl j)) && ((idxSr i) == (idxSr j)) = (i == j).
Proof.
case E1: (i == j); first by move/eqP: E1 => ->; rewrite !eqxx.
apply/negP. move/negP: E1. apply contra_not.
move/andP=> [/eqP/idxP eqSl /eqP/idxP eqSr].
apply/eqP; apply/idxP=> x; case E1: ((val x \in A) == true);
[move: (eqSl (setsub (elimTF eqP E1))) | move: (eqSr (setsub (subInR (elimTF eqP E1))))];
rewrite /idxSl !idxE /incl /=; destruct x => //=;
by rewrite !(eq_irrelevance (subsetP _ _ _) i0).
Qed.

Definition idxR A B (subST: A :<=: B) (eAB : idx B) : idx A :=
  \idx[E]_ (i : A) eAB (incl subST i).

Lemma idxRA A B C (subST: A :<=: B) (subTW: B :<=: C) (eAB : idx C) : 
    idxR subST (idxR subTW eAB) = idxR (subset_trans subST subTW) eAB.
Proof.
apply/idxP=>i; rewrite !idxE/=; rewrite /incl /=.
by congr (eAB (exist _ _ _)); apply eq_irrelevance.
Qed.

Lemma idxR_castL A A' B (eqS: A = A') subST subS'B (eAB : idx B) :
    castidx eqS (idxR subST eAB) = idxR subS'B eAB.
Proof. 
case: A' / eqS subS'B => P. 
by rewrite castidx_id (eq_irrelevance subST P).
Qed.

Lemma idxR_castR A B B' (eqT: B = B') subST subST' (eAB : idx B) :
    (idxR subST' (castidx eqT eAB) : idx A) = idxR subST eAB.
Proof. 
case: B' / eqT subST' => P. 
by rewrite castidx_id (eq_irrelevance subST P).
Qed.

Lemma idxSl_idxR A B (i : idx (A :|: B)) :
    idxSl i = idxR (subsetUl A B) i.
Proof. by []. Qed.

Lemma idxSr_idxR A B (i : idx (A :|: B)) :
    idxSr i = idxR (subsetUr A B) i.
Proof. by []. Qed.

Lemma idxR_id A (eqS: A :<=: A) (eAB : idx A) : 
    idxR eqS eAB = eAB.
Proof. 
rewrite /idxR; apply/idxP=>i; rewrite !idxE /incl; destruct i.
by congr (eAB (exist _ _ _)); apply eq_irrelevance.
Qed.

Definition idxR_cast := (idxR_castL, idxR_castR).
Definition idxS_idxR := (idxSl_idxR, idxSr_idxR).

Lemma castidxs0 A (i : idx (A :|: set0)) :
  idxSl i = castidx (setU0 A) i.
Proof.
rewrite ?idxS_idxR -[RHS]idxR_id idxR_castR ?setU0// =>H; 
by f_equal; apply eq_irrelevance.
Qed.

Lemma castidx0s A (i : idx (set0 :|: A)) :
  idxSr i = castidx (set0U A) i.
Proof.
rewrite ?idxS_idxR -[RHS]idxR_id idxR_castR ?set0U// =>H; 
by f_equal; apply eq_irrelevance.
Qed.

Lemma idxSsum A B (V : zmodType) (F: idx (A :|: B) -> V) :
  [disjoint A & B] -> \sum_i F i = \sum_(i : idx A) \sum_(j : idx B) F (idxU i j).
Proof.
rewrite sig_big_dep /==>H. symmetry.
rewrite [RHS](eq_bigr (fun x=> F (idxU (idxSl x) (idxSr x)))).
move=>i _. apply f_equal. by rewrite idxUS.
apply: (reindex (fun x => Tagged (fun=> idx B) (idxSr x))).
exists (fun x => idxU (projT1 x) (projT2 x)) => -[].
by move=> d _; rewrite -[RHS]idxUS.
move=>/=l r P1; rewrite /Tagged; congr (existT _ _ _); last by rewrite idxSUr.
apply/idxP=> i; by rewrite idxE idxUEl.
Qed.

Lemma idx_big_recl_cast (n : nat) (dt : n.+1.-tuple {set I}) :
  dt ~_ ord0 :|: \bigcup_i dt ~_ (fintype.lift ord0 i) = \bigcup_i dt ~_ i.
Proof. by rewrite big_ord_recl. Qed.

Lemma castidx_app (J : finType) (F : J -> chsType) (S1 S2 : {set J})
  (eq_S : S1 = S2) (A1 : 'Idx[F]_S1) (x : { i : J | i \in S2 }) :
  castidx eq_S A1 x =
    A1 (@exist J (fun i : J => i \in S1)
       (tag x)
       (ecast z (tag x \in z) (esym eq_S) (tagged x))).
Proof.
case: x => x xS2; case: A1=> /= d; rewrite /fun_of_mvector /=.
rewrite /castidx; case: _ / eq_S x xS2 d => x xS2 d /=.
set xS2':= ssrfun.svalP _; by rewrite (eq_irrelevance xS2 xS2').
Qed.

(* split is always better then pack, since split is inj *)
(* similarly, flatidx is better then packidx *)
Lemma idx_big_recl (n : nat) (dt : n.+1.-tuple {set I}) (e : idx (\bigcup_i dt ~_ i)) j :
  flatidx (idxSr (castidx (esym (idx_big_recl_cast dt)) e)) j
  = flatidx e (fintype.lift ord0 j).
Proof.
rewrite /flatidx /= !ffunE; apply/idxP => /= i; rewrite !idxE.
rewrite castidx_app /=; apply/val_inj => /=; congr (e _) => /=.
by apply/val_inj.
Qed.

Lemma idx_big_recl0 (n : nat) (dt : n.+1.-tuple {set I}) (e : idx (\bigcup_i dt ~_ i)) :
  ((flatidx e) ord0) = (idxSl (castidx (esym (idx_big_recl_cast dt)) e)).
Proof.
rewrite !ffunE; apply/idxP => /= i; rewrite !idxE.
rewrite castidx_app /=; apply/val_inj => /=.
by congr (e _) => /=; apply/val_inj => /=.
Qed.

End SetIndex.

(* tenor of state over disjoint set *)
(* note: tensor is defined for all cases, but only correct if domain are disjoint *)

HB.lock Definition tenv {I : finType} {E : I -> chsType} [A B: {set I}]
  (u : 'H[E]_A) (v : 'H_B) : 'H_(A :|: B) := 
  \sum_(e : 'Idx_(A :|: B)) (cdv (idxSl e) u * cdv (idxSr e) v) *: deltav e.

HB.lock Definition tenvm {I : finType} {E : I -> chsType} [J: finType] 
  [fs : J -> {set I}] (u : forall i : J, 'H[E]_(fs i)) := 
    injectv (\mvector_(i : J) u i).

(* tenor of lfun over disjoint domain *)
HB.lock Definition tenfm {I : finType} {E : I -> chsType} [J: finType] 
  [fs fs' : J -> {set I}] (u: forall i : J, 'F[E]_(fs i, fs' i)) := 
    injectf (\mvector_(i : J) u i).

Notation "f ⊗v g" := (tenv f g) : lfun_scope.

Section SetTensorProduct.
Context {I : finType} {E : I -> chsType}.

Implicit Type (A B: {set I}).
Local Notation idx := (@idx _ E).
Local Notation Hs := (@Hs _ E).
Local Notation Hf := (@Hf _ E).
Local Notation tenv := (@tenv I E).

Lemma tenv_dim A B (dis: [disjoint A & B]) :
  (dim (Hs (A :|: B)) = dim (Hs A) * dim (Hs B))%N.
Proof. by rewrite !dim_setten big_setU. Qed.

Definition tenv_indexl A B (i : 'I_(dim (Hs A) * dim (Hs B))) : 'I_(dim (Hs (A :|: B))) 
  := i2n (idxU (n2i (mxtens_unindex i).1) (n2i (mxtens_unindex i).2)).

Definition tenv_indexr A B (i : 'I_(dim (Hs (A :|: B)))) : 'I_(dim (Hs A) * dim (Hs B)) 
  := mxtens_index (i2n (idxSl (@n2i I E (A :|: B) i)), i2n (idxSr (n2i i))).

Lemma tenv_indexlK {A B} (dis: [disjoint A & B]) : 
  cancel (@tenv_indexl A B) (@tenv_indexr _ _).
Proof.
by move=>i; rewrite /tenv_indexl /tenv_indexr/= i2nK idxSUl idxSUr// !n2iK mxtens_unindexK.
Qed.

Lemma tenv_indexrK {A B} : 
  cancel (@tenv_indexr A B) (@tenv_indexl A B).
Proof.
by move=>i; rewrite /tenv_indexl /tenv_indexr mxtens_indexK/= !i2nK idxUS n2iK.
Qed.

Definition tenv_mxU {A B: {set I}} : 'M[C]_(_,_) :=
  \matrix_(i,j) (@tenv_indexr A B i == j)%:R.

Lemma tenv_mxU_unitarymx A B :
  (@tenv_mxU A B) \is unitarymx.
Proof.
apply/unitarymxP/matrixP=>i j; rewrite -adjmxE !mxE.
rewrite (bigD1 (tenv_indexr i))//= big1=>[k /negPf nki|].
by rewrite mxE eq_sym nki mul0r.
by rewrite mxE eqxx mul1r !mxE (can_eq tenv_indexrK) eq_sym conjC_nat addr0.
Qed.

Lemma tenv_mxU_adj_unitarymx A B (dis: [disjoint A & B]) :
  (@tenv_mxU A B)^*t \is unitarymx.
Proof.
apply/unitarymxP/matrixP=>i j; rewrite -adjmxE !mxE.
rewrite (bigD1 (tenv_indexl i))//= big1=>[k /negPf nki|].
by rewrite !mxE (can2_eq tenv_indexrK (tenv_indexlK dis)) nki conjC0 mul0r.
by rewrite !mxE (tenv_indexlK dis) eqxx conjC1 conjCK mul1r addr0.
Qed.

Lemma tenv_h2cE A B (u : Hs A) (v : Hs B) :
  h2c (u ⊗v v) = tenv_mxU *m (h2c u *t h2c v).
Proof.
have P0: mxtens_index (ord0,ord0) = 0 :> 'I_(1 * 1) by rewrite ord1.
apply/matrixP=>i j; rewrite tenv.unlock [in RHS](dec_dv u) [in RHS](dec_dv v) 
  !linear_sum/= linear_suml/= linear_sumr/= !summxE ord1.
rewrite (bigD1 (n2i i))//= big1=>[k /negPf nki|].
  by rewrite linearZ/= mxE deltav.unlock h2c_eb mxE eqxx andbT
    -(can2_eq (@n2iK _ _ _) (@i2nK _ _ _)) eq_sym nki mulr0.
rewrite addr0 linearZ/= deltav.unlock h2c_eb n2iK !mxE !eqxx mulr1.
rewrite (bigD1 (n2i (mxtens_unindex (tenv_indexr i)).1))// 
  !mxtens_indexK i2nK/= [X in _ + X]big1.
  move=>k /negPf nki; rewrite mxE big1//==>l _.
  case: (mxtens_indexP l)=>la lb.
  rewrite -P0 tensmxE linearZ/= h2c_eb !mxE.
  case: eqP; last by rewrite mul0r.
  move=>/(can_inj (@mxtens_indexK _ _))=>Pv; inversion Pv.
  by rewrite (inj_eq (@i2n_inj _ _ _)) eq_sym nki/= mulr0 mul0r mulr0.
rewrite linear_sumr/= linear_sumr/= summxE.
rewrite (bigD1 (n2i (mxtens_unindex (tenv_indexr i)).2))// !mxtens_indexK/= i2nK big1.
  move=>k /negPf nki; rewrite mxE big1//==>l _.
  case: (mxtens_indexP l)=>la lb.
  rewrite -P0 tensmxE linearZ/= h2c_eb !mxE.
  case: eqP; last by rewrite mul0r.
  move=>/(can_inj (@mxtens_indexK _ _))=>Pv; inversion Pv.
  by rewrite !eqxx/= linearZ/= h2c_eb !mxE (inj_eq (@i2n_inj _ _ _)) eq_sym nki/= !mulr0.
rewrite !addr0 !linearZ/= !h2c_eb mxE (bigD1 (tenv_indexr i))//= big1.
  by move=>k /negPf nki; rewrite mxE eq_sym nki mul0r.
by rewrite addr0 -{3}P0 tensmxE !mxE !eqxx !mulr1 mul1r.
Qed.

Lemma linear_tenv A B u : linear (@tenv A B u).
Proof. 
move=>a v w; rewrite tenv.unlock linear_sum -big_split; apply eq_bigr=>i _.
by rewrite linearP/= mulrDr scalerDl scalerA mulrA [_ * a]mulrC mulrA.
Qed.
HB.instance Definition _ A B u := GRing.isLinear.Build C 'H[E]_B 'H_(A :|: B) 
  *:%R (@tenv A B u) (@linear_tenv A B u).

Lemma linear_tenvr A B u : linear ((@tenv A B)^~ u).
Proof.
move=>a v w; rewrite tenv.unlock linear_sum -big_split; apply eq_bigr=>i _.
by rewrite linearP/= mulrDl scalerDl scalerA mulrA.
Qed.
HB.instance Definition _ A B := bilinear_isBilinear.Build C 'H[E]_A 'H_B
  'H_(A :|: B) *:%R *:%R (@tenv A B) (@linear_tenvr A B, @linear_tenv A B).

Lemma tenv0 A B (u: Hs A) : u ⊗v (0: Hs B) = 0.
Proof. exact: linear0r. Qed.
Lemma tenvNl A B (v: Hs B) (u: Hs A) : (-u) ⊗v v = - (u ⊗v v).
Proof. exact: linearNl. Qed.
Lemma tenvBl A B (w: Hs B) (u v: Hs A) : (u-v) ⊗v w = u ⊗v w - v ⊗v w.
Proof. exact: linearBl. Qed.
Lemma tenvDl A B (w: Hs B) (u v: Hs A) : (u+v) ⊗v w = u ⊗v w + v ⊗v w.
Proof. exact: linearDl. Qed.
Lemma tenvZl A B (v: Hs B) (c: C) (u: Hs A) : (c*:u) ⊗v v = c *: (u ⊗v v).
Proof. exact: linearZl_LR. Qed.
Lemma tenvPl A B (w: Hs B) (c: C) (u v: Hs A) : 
  (c*:u+v) ⊗v w = c *: (u ⊗v w) + v ⊗v w.
Proof. exact: linearPl. Qed.
Lemma tenvMnl A B (v: Hs B) (u: Hs A) n : (u *+ n) ⊗v v = (u ⊗v v) *+ n.
Proof. exact: linearMnl. Qed.
Lemma tenvMNnl A B (v: Hs B) (u: Hs A) n : tenv (u *- n) v = (tenv u v) *- n.
Proof. exact: linearMNnl. Qed.
Lemma tenv_suml L r (P : pred L) A B (F: L -> Hs A) (u: Hs B) : 
  (\sum_(i <- r | P i) F i) ⊗v u = \sum_(i <- r | P i) ((F i) ⊗v u).
Proof. exact: linear_suml. Qed.
Lemma ten0v A B (u: Hs B) : (0: Hs A) ⊗v u = 0.
Proof. exact: linear0l. Qed.
Lemma tenvNr A B (u: Hs A) (v: Hs B) : u ⊗v (-v) = - (u ⊗v v).
Proof. exact: linearNr. Qed.
Lemma tenvBr A B (w: Hs A) (u v: Hs B) : w ⊗v (u-v) = w ⊗v u - w ⊗v v.
Proof. exact: linearBr. Qed.
Lemma tenvDr A B (w: Hs A) (u v: Hs B) : w ⊗v (u+v) = w ⊗v u + w ⊗v v.
Proof. exact: linearDr. Qed.
Lemma tenvZr A B (v: Hs A) (c: C) (u: Hs B) : v ⊗v (c*:u) = c *: (v ⊗v u).
Proof. exact: linearZr. Qed.
Lemma tenvPr A B (w: Hs A) (c: C) (u v: Hs B) : 
  w ⊗v (c *: u + v) = c *: (w ⊗v u) + (w ⊗v v).
Proof. exact: linearPr. Qed.
Lemma tenvMnr A B (v: Hs A) (u: Hs B) n : v ⊗v (u *+ n) = (v ⊗v u) *+ n.
Proof. exact: linearMnr. Qed.
Lemma tenvMNnr A B (v: Hs A) (u: Hs B) n : v ⊗v (u *- n) = (v ⊗v u) *- n.
Proof. exact: linearMNnr. Qed.
Lemma tenv_sumr L r (P : pred L) A B (u: Hs A) (F: L -> Hs B)  : 
  u ⊗v (\sum_(i <- r | P i) F i) = \sum_(i <- r | P i) (u ⊗v (F i)).
Proof. exact: linear_sumr. Qed.

Lemma tenv_dot A B (u1 u2 : Hs A) (v1 v2 : Hs B) : 
  [disjoint A & B] -> [< u1 ⊗v v1 ; u2 ⊗v v2 >] = [< u1 ; u2>] * [< v1 ; v2 >].
Proof.
move=>dis; rewrite !dotp_mulmx !tenv_h2cE -!trace_mx11.
rewrite adjmxM mulmxA mulmxKtV ?tenv_mxU_unitarymx// ?tenv_dim//.
by rewrite (adjmx_tens (h2c u1) (h2c v1)) 
  (tensmx_mul (h2c u1)^*t (h2c v1)^*t (h2c u2) (h2c v2)) -mxtrace_tens.
Qed.

Lemma tenv_norm A B (u : Hs A) (v : Hs B) : 
  [disjoint A & B] -> `|u ⊗v v| = `|u| * `|v|.
Proof. by move=>P; rewrite !hnormE tenv_dot// sqrtCM// dotp_norm nnegrE exprn_ge0. Qed.

Lemma cdv_norm A (u : Hs A) : `|u| = sqrtC (\sum_i `|cdv i u|^+2).
Proof.
rewrite hnormE; f_equal.
rewrite {1 2}(dec_dv u) dotp_suml; apply eq_bigr=>/= i _.
rewrite dotp_sumr (bigD1 i)//= big1=>[j/negPf nji|].
by rewrite dotpZl dotpZr dv_dot eq_sym nji !mulr0.
by rewrite dotpZl dotpZr dv_dot eqxx mulr1 addr0 normCKC.
Qed.

Lemma cdvT A B u v (i : idx (A :|: B)) : 
  cdv i (u ⊗v v) = cdv (idxSl i) u * cdv (idxSr i) v.
Proof.
rewrite tenv.unlock linear_sum/= (bigD1 i)// big1//=.
by move=>j /negPf nji; rewrite linearZ/= cdv_dv eq_sym nji mulr0.
by rewrite addr0 linearZ/= cdv_dv eqxx mulr1.
Qed.

Lemma tenv_norm_le A B (u : Hs A) (v : Hs B) : 
  `|u ⊗v v| <= `|u| * `|v|.
Proof.
rewrite !cdv_norm -sqrtCM ?ler_sqrtC ?nnegrE ?mulr_ge0//.
1-5: by rewrite sumr_ge0//= =>? _; rewrite exprn_ge0.
pose Pi (i : idx A * idx B) := (idxSl (idxU i.1 i.2) == i.1) && (idxSr (idxU i.1 i.2) == i.2).
rewrite big_distrlr/= pair_big/= (bigID Pi)/=.
apply: ler_wpDr; first by apply sumr_ge0=>? _; rewrite mulr_ge0// exprn_ge0.
under eq_bigr do rewrite cdvT normrM exprMn.
rewrite -[X in _ <= X]big_sig/=.
have P1 (x : idx (A :|: B)) : Pi (idxSl x, idxSr x).
by rewrite /Pi /= idxUS !eqxx.
pose h (x : idx (A :|: B)) := exist Pi _ (P1 x).
rewrite (reindex h)//=.
exists (fun i => idxU (val i).1 (val i).2).
by move=>i _; rewrite /h/= idxUS.
move=>i _; case: i=>[[i1 i2]] p; apply/val_inj=>/=.
by move: p=>/andP[]/=/eqP->/eqP->.
Qed.

Lemma dv_split A B (i: idx (A :|: B)) :
  deltav i = (deltav (idxSl i)) ⊗v (deltav (idxSr i)).
Proof. by apply/cdvP=>j; rewrite cdvT !cdv_dv -idxBE -mulnb natrM. Qed.

Lemma dv_tensor A B (i : idx A) (j : idx B) :
  [disjoint A & B] -> (deltav i) ⊗v (deltav j) = deltav (idxU i j).
Proof. by move=>dis; rewrite dv_split ?idxSUl ?idxSUr. Qed.

Lemma tenv_dv_eq0 A B (i1 : 'Idx[E]_A) (i2 : 'Idx_B) :
  (idxSl (idxU i1 i2) != i1) || (idxSr (idxU i1 i2) != i2) -> 
    deltav i1 ⊗v deltav i2 = 0.
Proof.
move=>P0; rewrite tenv.unlock big1// =>i _; rewrite !cdv_dv.
case: eqP; case: eqP=>/=; rewrite ?mulr0 ?mul0r ?scale0r// =>P1 P2.
suff: idxU i1 i2 = i by move=>P; move: P0; rewrite P P1 P2 !eqxx.
apply/idxP=>j; rewrite/idxU idxE; case: eqP=>P.
- move: P2=>/idxP=>/(_ (setsub P))=><-; rewrite /idxSl idxE.
  by case: j P=>j Pj/= P; rewrite /incl/= (eq_irrelevance (subsetP _ _ _) Pj).
- move: P1=>/idxP=>/(_ (setsub (subInR P)))=><-; rewrite /idxSr idxE.
  by case: j P=>j Pj/= P; rewrite /incl/= (eq_irrelevance (subsetP _ _ _) Pj).
Qed.

Lemma tenv_conj A B (u: Hs A) (v: Hs B) : ((u^*v) ⊗v (v^*v) = (u ⊗v v)^*v)%VF.
Proof.
rewrite (dec_dv u) raddf_sum/= !linear_suml raddf_sum/=; apply eq_bigr=>i _. 
rewrite (dec_dv v) raddf_sum/= linear_sum linear_sumr raddf_sum/=.
apply eq_bigr=>j _; rewrite !conjvZ !linearZl_LR !linearZr/= !conjvZ.
congr (_ *: (_ *: _)); rewrite !conj_dv; apply/cdvP=>k.
by rewrite conj_cdv !cdvT rmorphM -!conj_cdv !conj_dv.
Qed.

Lemma tenv_castA S1 S2 S3 (u: 'H[E]_S1) (v: 'H_S2) (w: 'H_S3) :
  casths (setUA S1 S2 S3) (u ⊗v (v ⊗v w)) = ((u ⊗v v) ⊗v w).
Proof.
apply/cdvP=>/= i; rewrite cdv_castV !cdvT mulrA.
do ? [apply f_equal2 | apply f_equal] =>//;
rewrite ?idxSl_idxR ?idxSr_idxR ?idxR_castR -?setUA ?subsetUl ?subsetUr// => H1; 
rewrite !idxRA; by do ? [apply f_equal2 | apply eq_irrelevance].
Qed.

Lemma tenv_castC S1 S2 (u: 'H[E]_S1) (v: 'H_S2) : 
  casths (setUC S1 S2) (u ⊗v v) = (v ⊗v u).
Proof.
apply/cdvP=>/= j; rewrite cdv_castV !cdvT mulrC.
do ? [apply f_equal2 | apply f_equal] =>//; 
    rewrite ?idxS_idxR ?idxR_cast ?subsetUl ?subsetUr// => H1;
    by do ? [apply f_equal2 | apply eq_irrelevance].
Qed.

Lemma tenv_idx0r A (u : Hs A) : 
  u ⊗v (deltav idx0) = casths (esym (setU0 _)) u.
Proof.
by apply/cdvP=>i; rewrite cdvT cdv_dv idx0E eqxx mulr1 cdv_castV esymK castidxs0.
Qed.

Lemma tenvm_dim (J: finType) (fs : J -> {set I}) : disf fs ->
  (dim (Hs (\bigcup_i fs i)) = \prod_i dim (Hs (fs i)))%N.
Proof. 
move=> dis; rewrite dim_setten partition_disjoint_bigcup//.
by apply eq_bigr=>i _; rewrite dim_setten.
Qed.

(* tenor of state over disjoint set *)

Lemma dv_splitm (J: finType) (fs : J -> {set I}) (i : idx (\bigcup_i (fs i))) :
  deltav i = tenvm (fun k=>deltav (flatidx i k)).
Proof. rewrite tenvm.unlock; exact: deltavm. Qed.

Lemma tenvm_dv_eq0 (J : finType) (A : J -> {set I}) (i : forall j : J,  'Idx[E]_(A j)) :
  [exists j, flatidx (packidx [ffun j => i j]) j != i j] -> 
    tenvm (fun j => deltav (i j)) = 0.
Proof.
move=>/existsP[j0 /negPf Pj0]; apply/eqP.
rewrite -dotp_eq0 tenvm.unlock injectv.unlock dotp_suml big1// =>j _.
rewrite dotp_sumr big1// =>k _.
rewrite dotpZl dotpZr dv_dot; case: eqP=>[->|]; last by rewrite !mulr0.
rewrite mulr1 - normCKC; apply/eqP; rewrite sqrf_eq0 normr_eq0.
under eq_bigr do rewrite prodvect.mvE cdv_dv.
suff: [exists j, flatidx k j != i j].
  by move=>/existsP[j1 /negPf Pj1]; rewrite (bigD1 j1)//= Pj1 mul0r.
rewrite - negb_forall; apply/negP=>/forallP P1.
have P2: flatidx k = [ffun j => i j]
  by apply/ffunP=>l; move: (P1 l)=>/eqP; rewrite ffunE.
by move: Pj0; rewrite -P2 flatidxK P1.
Qed.

Lemma tenvm_dot (J: finType) (fs : J -> {set I})
  (u v: forall i : J, Hs (fs i)) : disf fs ->
  [< tenvm u ; tenvm v >] = \prod_i [< u i ; v i >].
Proof.
move=> dis; rewrite tenvm.unlock -injectv_dot// /hdotp.
by under eq_bigr do rewrite !mvE.
Qed.

Lemma cdv_tm (J: finType) (fs : J -> {set I})
  (x: forall i : J, Hs (fs i)) e : 
  cdv e (tenvm x) = \prod_i cdv (flatidx e i) (x i).
Proof.
rewrite tenvm.unlock injectv.unlock linear_sum/= (bigD1 e)//= [X in X + _]linearZ.  
rewrite /= cdv_dv eqxx mulr1 [X in _ + X]big1 ?addr0 =>[i/negPf ni|].
by rewrite linearZ/= cdv_dv eq_sym ni mulr0.
by under eq_bigr do rewrite mvE.
Qed.

Lemma tenvmP (J: finType) (fs : J -> {set I}) (x y : forall i : J, Hs (fs i)) :
  (forall i, x i = y i) -> tenvm x = tenvm y.
Proof. by move=>P; apply/cdvP=>i; rewrite !cdv_tm; under eq_bigr do rewrite P. Qed.

Lemma tenvm0 (J : finType) (A : J -> {set I}) (i : forall j : J,  'H[E]_(A j)) :
    (exists j, i j = 0) -> tenvm i = 0.
Proof.
move=>[j Pj]; rewrite tenvm.unlock; apply/tensor.mlinear0.
by apply injectv_mlinear.
by exists j; rewrite prodvect.mvE.
Qed.

Lemma tenvm_conj (J: finType) (fs : J -> {set I}) (x: forall i : J, Hs (fs i)) :
  ((tenvm x)^*v = tenvm (fun i=> (x i)^*v))%VF.
Proof.
apply/cdvP=>i; rewrite conj_cdv !cdv_tm rmorph_prod; 
by apply eq_bigr=>j _; rewrite conj_cdv.
Qed.

Lemma tenvm_recl (n : nat) (dt : n.+1.-tuple {set I}) 
  (u : forall x : 'I_n.+1, Hs (dt ~_ x)) :
  casths (esym (idx_big_recl_cast dt)) (tenvm u) = 
    (u ord0 ⊗v tenvm (fun i=> (u (fintype.lift ord0 i)))).
Proof.
apply/cdvP=>i; rewrite cdvT cdv_castV esymK !cdv_tm big_ord_recl; f_equal.
by rewrite idx_big_recl0 castidx_comp castidx_id.
by apply eq_bigr=>/= j _; f_equal; rewrite -idx_big_recl castidx_comp castidx_id.
Qed.

Lemma tenvmZ (J: finType) (fs : J -> {set I}) (a : forall i : J, C) 
  (x: forall i : J, Hs (fs i)) :
    (tenvm (fun i => a i *: x i)) = (\prod_i a i) *: tenvm x.
Proof.
rewrite tenvm.unlock -mlinearZm. exact: injectv_mlinear.
by f_equal; apply/mvectorP=>i; rewrite !mvE.
Qed.

Lemma tenvm_sum (J: finType) (fs : J -> {set I}) (K : J -> finType)
  (x: forall i : J, (K i) -> Hs (fs i)) :
    (tenvm (fun i => \sum_j x i j)) = 
      \sum_(b : mvector (fun i : J => (K i))) tenvm (fun i => x i (b i)).
Proof. by rewrite tenvm.unlock (mlinear_sum x (@injectv_mlinear _ _ _ _)). Qed.

End SetTensorProduct.

(* TODO : move *)
Section DefaultONB.
Variable (L : finType) (H : L -> chsType).

Lemma idx_card (S : {set L}) :
  #|'Idx[H]_S| = dim 'H[H]_S.
Proof. by  rewrite card_idx dim_setten. Qed.

HB.instance Definition _ (S : {set L}) := isONB.Build 
  'H[H]_S 'Idx[H]_S deltav (@dv_dot L H S) (idx_card S).

HB.instance Definition _ (S : {set L}) (i : 'Idx[H]_S) := 
  NormalState.copy (deltav i) ((@deltav L H S : 'ONB) i : 'NS).

End DefaultONB.

(* tenor product of linear function, onbasis free *)
(* note that tenor is defined for all cases, but only correct if domains/codomains 
   are disjoint *)
HB.lock Definition ten_lfun_fun {I : finType} {E : I -> chsType} 
  [S T S' T'] (f: 'F[E]_(S,T)) (g: 'F_(S',T')) (u : 'H_(S :|: S')) := 
    \sum_(i : 'Idx_(S :|: S')) cdv i u *:
      ((f (deltav (idxSl i))) ⊗v (g (deltav (idxSr i)))).

Lemma ten_lfun_fun_is_linear {I : finType} {E : I -> chsType} 
  [S T S' T'] (f: 'F[E]_(S,T)) (g: 'F_(S',T')) :
  linear (ten_lfun_fun f g).
Proof.
move=>a u v; rewrite ten_lfun_fun.unlock scaler_sumr -big_split /=.
by apply eq_bigr=>i _; rewrite scalerA -scalerDl linearP.
Qed.
HB.instance Definition _ {I : finType} {E : I -> chsType} [S T S' T'] 
  (f: 'F[E]_(S,T)) (g: 'F_(S',T')):= GRing.isLinear.Build 
    C 'H_(S :|: S') 'H_(T :|: T') *:%R (ten_lfun_fun f g)
      (ten_lfun_fun_is_linear f g).
Definition ten_lfun {I : finType} {E : I -> chsType} [S T S' T'] 
  (f: 'F[E]_(S,T)) (g: 'F_(S',T')) := linfun (ten_lfun_fun f g).

(* with auto-lifting *)
HB.lock Definition dot_lfun {I : finType} {E : I -> chsType} [S T S' T'] 
  (f: 'F[E]_(S,T)) (g: 'F_(S',T')) :=
    ((ten_lfun f (\1: 'F_(T' :\: S, T' :\: S))) \o castlf (erefl _, (setUDS T' S))
      (ten_lfun g (\1: 'F_(S :\: T', S :\: T'))))%VF.

(* for the case that both f and g are square *)
HB.lock Definition sdot_lfun {I : finType} {E : I -> chsType} [S T] (f : 'F[E]_S) (g : 'F_T) :=
    castlf (setUDV _ _, (setUD _ _)) (dot_lfun f g).

Notation "f \⊗ g" := (ten_lfun f g) (at level 45, left associativity) : lfun_scope.
Notation "f \· g" := (dot_lfun f g) (at level 40, left associativity) : lfun_scope.
Notation "f \O g" := (sdot_lfun f g) (at level 40, left associativity) : lfun_scope.

Section LinfunDef.
Context {I : finType} {E : I -> chsType}.
Implicit Type (S T W: {set I}).
Local Notation v0 := (deltav (@idx0 _ E)).

Let dotp_dv0Z (V : lmodType C) (f : V) : [< v0; v0 >] *: f = f.
Proof. by rewrite dv_dot eqxx scale1r. Qed.
Lemma outp_dv0 : [> v0; v0 <] = \1.
Proof. by apply/lfunPD=>i; rewrite !idx0E outpE dv_dot eqxx scale1r lfunE. Qed.
Lemma cdv0E v : cdv idx0 v = [< v0 ; v >]. Proof. by rewrite cdvE. Qed.

(* translform between vector 'H[H]_S and linfun 'FV[H]_S *)
Definition s2sv (a : C) : 'H[E]_set0 := a *: v0.
Definition sv2s (v : 'H[E]_set0) : C := [< v0 ; v >].
Definition s2sf (a : C) : 'F[E]_set0 := a *: \1.
Definition sf2s (f : 'F[E]_set0) : C := [< v0; f v0 >].
Definition v2f S (v : 'H[E]_S) := [> v ; v0 <].
Definition f2v S (f : 'FV[E]_S) := f v0.
Definition v2df S (v : 'H[E]_S) := [> v0 ; v <].
Definition df2v S (f : 'FdV[E]_S) := f^A v0.

Lemma dec_sv v : v = cdv idx0 v *: v0.
Proof. by rewrite cdv0E -outpE outp_dv0 lfunE. Qed.

Lemma sv_normE (v: 'H[E]_set0) :  `|v| = `|cdv idx0 v|.
Proof. by rewrite {1}(dec_sv v) hnormZ dv_norm mulr1. Qed.

Lemma s2sv_is_additive : additive s2sv.
Proof. by move=>u v; rewrite /s2sv scalerDl scaleNr. Qed.
HB.instance Definition _ := GRing.isAdditive.Build 
  C 'H[E]_set0 s2sv s2sv_is_additive.
HB.instance Definition _ := GRing.Linear.copy sv2s (sv2s : {linear _ -> _}).
Lemma s2sf_is_additive : additive s2sf.
Proof. by move=>a b; rewrite /s2sf scalerBl. Qed.
HB.instance Definition _ := GRing.isAdditive.Build 
  C 'F[E]_set0 s2sf s2sf_is_additive.
Lemma sf2s_is_scalar : scalar sf2s.
Proof. by move=> a x y; rewrite /sf2s lfunE /= scale_lfunE; rewrite linearP. Qed.
HB.instance Definition _ := GRing.isLinear.Build 
  C 'F[E]_set0 C *%R sf2s sf2s_is_scalar.
Lemma v2f_is_linear S : linear (@v2f S). Proof. exact: linearPl. Qed.
HB.instance Definition _ S := GRing.isLinear.Build 
  C 'H[E]_S 'FV_S *:%R (@v2f S) (@v2f_is_linear S).
Lemma f2v_is_linear S : linear (@f2v S).
Proof. by move=>a f g; rewrite /f2v; do ? rewrite lfunE/=. Qed.
HB.instance Definition _ S := GRing.isLinear.Build 
  C 'FV_S 'H[E]_S *:%R (@f2v S) (@f2v_is_linear S).
HB.instance Definition _ S := GRing.Linear.copy 
  (@v2df S) (@v2df S : {linear _ -> _ | _}).
Lemma df2v_is_antilinear S : antilinear (@df2v S).
Proof. by move=>a f g; rewrite/df2v linearP/= lfunE/= lfunE. Qed.
HB.instance Definition _ S := GRing.isLinear.Build 
  C 'FdV_S 'H[E]_S (Num.conj_op \;  *:%R) (@df2v S) (@df2v_is_antilinear S).

Lemma s2svK : cancel s2sv sv2s.
Proof. by move=>u; rewrite/sv2s/s2sv/cdv dotpZr dv_dot eqxx mulr1. Qed.
Lemma sv2sK : cancel sv2s s2sv.
Proof. by move=>u; rewrite/sv2s/s2sv {2}[u]dec_sv cdvE. Qed.
Lemma s2sv_inj : injective s2sv. Proof. exact (can_inj s2svK). Qed.
Lemma sv2s_inj : injective sv2s. Proof. exact (can_inj sv2sK). Qed.
Lemma s2sfK : cancel s2sf sf2s.
Proof. by move=>a; rewrite/s2sf/sf2s lfunE/= lfunE/= dotpZr dv_dot eqxx mulr1. Qed.
Lemma sf2sK : cancel sf2s s2sf.
Proof.
by move=>a; apply/lfunP=>u; rewrite/s2sf/sf2s lfunE/= lfunE/= 
  -outpE (dec_sv u) linearZl_LR/= outp_dv0 lfunE/= lfunE/= linearZ.
Qed.
Lemma s2sf_inj : injective s2sf. Proof. exact (can_inj s2sfK). Qed.
Lemma sf2s_inj : injective sf2s. Proof. exact (can_inj sf2sK). Qed.
Lemma v2fK S : cancel (@v2f S) (@f2v S). Proof. by move=>v; rewrite/f2v outpE. Qed.
Lemma f2vK S : cancel (@f2v S) (@v2f S).
Proof. by move=>v; apply/lfunP=>u; rewrite/v2f/f2v outpE {2}(dec_sv u) cdvE linearZ. Qed.
Lemma v2f_inj S : injective (@v2f S). Proof. exact (can_inj (@v2fK S)). Qed.
Lemma f2v_inj S : injective (@f2v S). Proof. exact (can_inj (@f2vK S)). Qed.
Lemma v2dfK S : cancel (@v2df S) (@df2v S).
Proof. by move=>v; rewrite/df2v/v2df adj_outp outpE. Qed.
Lemma df2vK S : cancel (@df2v S) (@v2df S).
Proof. by move=>v; apply/lfunP=>u; rewrite outpE adj_dotEl [RHS]dec_sv cdvE. Qed.
Lemma v2df_inj S : injective (@v2df S). Proof. exact (can_inj (@v2dfK S)). Qed.
Lemma df2v_inj S : injective (@df2v S). Proof. exact (can_inj (@df2vK S)). Qed.

Lemma s2sv_conj c : (s2sv c)^*v = s2sv (c^*).
Proof. by rewrite/s2sv conjvZ conj_dv. Qed.
Lemma sv2s_conj u : (sv2s u)^* = sv2s (u ^*v).
Proof. by apply s2sv_inj; rewrite -s2sv_conj !sv2sK. Qed.
Lemma s2sf_conj c : (s2sf c)^C = s2sf (c^*).
Proof. by rewrite/s2sf conjfZ conjf1. Qed.
Lemma sf2s_conj f : (sf2s f)^* = sf2s (f^C ).
Proof. by apply s2sf_inj; rewrite -s2sf_conj !sf2sK. Qed.
Lemma v2f_conj S (u : 'H_S) : (v2f u)^C = v2f (u ^*v).
Proof. by rewrite/v2f conj_outp conj_dv. Qed.
Lemma f2v_conj S (f : 'FV_S) : (f2v f)^*v = f2v (f^C ).
Proof. by apply v2f_inj; rewrite -v2f_conj !f2vK. Qed.
Lemma v2df_conj S (u: 'H_S) : (v2df u)^C = v2df u^*v.
Proof. by rewrite/v2df conj_outp conj_dv. Qed.
Lemma df2v_conj S (f: 'FdV_S) : (df2v f)^*v = df2v f^C.
Proof. by apply v2df_inj; rewrite -v2df_conj !df2vK. Qed.

Lemma s2sf_adj c : (s2sf c)^A = s2sf c^*.
Proof. by rewrite/s2sf adjfZ adjf1. Qed.
Lemma sf2s_adj f : (sf2s f)^* = sf2s (f^A).
Proof. by rewrite/sf2s conj_dotp adj_dotEr. Qed.
Lemma v2f_adj S (u : 'H_S) : (v2f u)^A = v2df u.
Proof. by rewrite/v2f/v2df adj_outp. Qed.
Lemma v2df_adj S (u : 'H_S) : (v2df u)^A = v2f u.
Proof. by rewrite -v2f_adj adjfK. Qed.
Lemma f2v_adj S (f: 'FdV_S) : f2v (f^A) = df2v f.
Proof. by []. Qed.
Lemma df2v_adj S (f: 'FV_S) : df2v (f^A) = f2v f.
Proof. by rewrite/df2v adjfK. Qed.

Lemma sfT (f : 'F[E]_set0) : f^T = f.
Proof. by apply/h2mx_inj/matrixP=>i j; rewrite tr_lfun.unlock mx2hK mxE (eq_nset0 j i). Qed.
Lemma sfAC (f : 'F[E]_set0) : f^A = f^C.
Proof. by rewrite adjfTC sfT. Qed.
Lemma v2f_tr S (u : 'H_S) : (v2f u)^T = v2df u^*v.
Proof. by rewrite trfAC v2f_adj v2df_conj. Qed.
Lemma v2df_tr S (u : 'H_S) : (v2df u)^T = v2f u^*v.
Proof. by rewrite trfAC v2df_adj v2f_conj. Qed.
Lemma f2v_tr S (f: 'FdV_S) : f2v f^T = df2v f^C.
Proof. by rewrite trfCA f2v_adj. Qed.
Lemma df2v_tr S (f: 'FV_S) : df2v (f^T) = (f2v f)^*v.
Proof. by rewrite trfAC -df2v_conj df2v_adj. Qed.

(* inner product of scalar vector *)
Lemma sv_dotp u v : [< u ; v >] = (sv2s u)^* * (sv2s v).
Proof. 
by rewrite {1}(dec_sv u) {1}(dec_sv v) !cdvE dotpZl dotpZr dv_dot eqxx mulr1 /sv2s.
Qed.

Lemma v2fE S (v : 'H_S) u : v2f v u = sv2s u *: v. Proof. exact: outpE. Qed.
Lemma v2dfE S (v u : 'H_S) : v2df v u = s2sv ([<v ; u>]). Proof. exact: outpE. Qed.

Lemma comp_dot S (u v : 'H_S) : ((v2df u) \o (v2f v))%VF = s2sf ([<u;v>]).
Proof. by rewrite outp_comp outp_dv0. Qed.

Lemma comp_norm S (v : 'H_S) : ((v2df v) \o (v2f v))%VF = s2sf (`|v| ^+ 2).
Proof. by rewrite comp_dot dotp_norm. Qed.

Lemma comp_out S T (u : 'H_S) (v : 'H_T) : (v2f u \o (v2df v))%VF = [>u ; v<].
Proof. by rewrite outp_comp dotp_dv0Z. Qed.

Lemma v2f_comp S T (f : 'F_(S, T)) v : f2v (f \o (v2f v)) = f v.
Proof. by rewrite/f2v outp_compr outpE. Qed.

Lemma v2df_comp S T (f : 'F_(S, T)) v : df2v (v2df v \o f) = f^A v.
Proof. by rewrite outp_compl/df2v adj_outp outpE. Qed.

Lemma tenf_dv S T S' T' (f: 'F[E]_(S,T)) (g: 'F[E]_(S',T')) i: 
  (f (deltav (idxSl i))) ⊗v (g (deltav (idxSr i))) = (ten_lfun f g) (deltav i).
Proof.
rewrite lfunE/= ten_lfun_fun.unlock (bigD1 i)// big1//=.
by move=>j /negPf nji; rewrite cdv_dv nji scale0r.
by rewrite cdv_dv eqxx scale1r addr0.
Qed.

Lemma tenf_outp S T S' T' (u : 'H[E]_S) (v : 'H_S') (w : 'H_T) (t : 'H_T'):
  [> u ; v <] \⊗ [> w ; t <] = [> u ⊗v w; v ⊗v t <].
Proof.
apply/lfunPD=>i; rewrite -tenf_dv !outpE linearZl_LR linearZr/= scalerA.
by f_equal; rewrite -[RHS]conj_dotp -cdvE cdvT !cdvE rmorphM !conj_dotp.
Qed.

Lemma linear_tenf S T S' T' f : linear (@ten_lfun I E S T S' T' f).
Proof.
move=>a v w; apply/lfunPD=>u; rewrite !lfunE/= !lfunE/= !lfunE/= ten_lfun_fun.unlock.
rewrite linear_sum /= -big_split; apply eq_bigr=>i _.
by rewrite !lfunE/= !lfunE/= !linearPr/= scalerDr !scalerA mulrC.
Qed.
HB.instance Definition _ S T S' T' f := GRing.isLinear.Build C 'F[E]_(S',T')
  'F_(S :|: S', T :|: T') *:%R (@ten_lfun I E S T S' T' f) (@linear_tenf S T S' T' f).
Lemma linear_tenfr S T S' T' f : linear ((@ten_lfun I E S T S' T')^~ f).
Proof.
move=>a v w; apply/lfunPD=>u; rewrite !lfunE/= !lfunE/= !lfunE/= ten_lfun_fun.unlock;
rewrite linear_sum /= -big_split; apply eq_bigr=>i _;
by rewrite !lfunE/= !lfunE/= !linearPl/= scalerDr !scalerA mulrC.
Qed.
HB.instance Definition _ S T S' T' := bilinear_isBilinear.Build C 'F[E]_(S,T) 'F[E]_(S',T')
  'F_(S :|: S', T :|: T') *:%R *:%R (@ten_lfun I E S T S' T') 
    (@linear_tenfr S T S' T', @linear_tenf S T S' T').

Lemma h2mx_tenf S T S' T' (f: 'F[E]_(S,T)) (g: 'F[E]_(S',T')) :
  h2mx (ten_lfun f g) = tenv_mxU *m (h2mx f *t h2mx g) *m tenv_mxU^*t.
Proof.
rewrite (onb_lfun2 deltav deltav f) (onb_lfun2 deltav deltav g) !pair_big/=.
rewrite !linear_suml/= !linear_sum/= linear_suml/= mulmx_sumr mulmx_suml.
apply eq_bigr=>[[i1 i2]] _ /=; rewrite !linear_sumr/= linear_sum/= mulmx_suml.
apply eq_bigr=>[[j1 j2]] _ /=; rewrite !linearZl/= !linearZ/= linearZl linearZr linearZl/=.
f_equal; rewrite !linearZr linearZl/=; f_equal.
by rewrite tenf_outp outp.unlock !mx2hK !tenv_h2cE adjmxM mulmxA mulmxACA -tensmx_mul -adjmx_tens.
Qed.

Lemma tenf_apply S T S' T' (f: 'F[E]_(S,T)) (g: 'F_(S',T')) : 
  [disjoint S & S'] ->
  forall u v, (f \⊗ g) (u ⊗v v) = (f u) ⊗v (g v).
Proof.
move=>dis u v; symmetry; rewrite {1}(dec_dv u) (dec_dv (tenv u v)).
rewrite !linear_sum linear_suml/= idxSsum//; apply eq_bigr=>i _.
rewrite {1}(dec_dv v) !linear_sum /=; apply eq_bigr=>j _.
rewrite !linearZ /= linearZl_LR/= -tenf_dv idxSUl// idxSUr// scalerA.
congr (_ *: _); rewrite tenv.unlock linear_sum/= (bigD1 (idxU i j))// big1/=.
by move=>k /negPf nki; rewrite linearZ/= cdv_dv eq_sym nki mulr0.
by rewrite idxSUl// idxSUr// linearZ/= cdv_dv eqxx mulr1 addr0 mulrC.
Qed.

Lemma tenf_comp S T S' T' W W' (f1: 'F[E]_(S,T)) (f2: 'F_(W,S)) 
  (g1: 'F_(S',T')) (g2: 'F_(W',S')) : [disjoint S & S'] ->
  (f1 \o f2) \⊗ (g1 \o g2) = (f1 \⊗ g1) \o (f2 \⊗ g2).
Proof.
move=>dis; apply/lfunPD=>i.
by rewrite comp_lfunE -!tenf_dv !comp_lfunE tenf_apply.
Qed.

Lemma tenf_conj S T S' T' (f: 'F[E]_(S,T)) (g: 'F_(S',T')) :
  (f \⊗ g)^C = f^C \⊗ g ^C.
Proof. by apply/lfunPD=>i; rewrite -tenf_dv !conjfE !conj_dv -tenf_dv tenv_conj. Qed.

Lemma tenf_adj S T S' T' (f: 'F[E]_(S,T)) (g: 'F_(S',T')) :
  (f \⊗ g)^A = f^A \⊗ g^A.
Proof. 
by apply/lfunPD=>i; apply/cdvP=>j; rewrite adj_cdv -!tenf_dv !cdvT !adj_cdv rmorphM.
Qed.

Lemma tenf_tr S T S' T' (f: 'F[E]_(S,T)) (g: 'F_(S',T')) :
  (f \⊗ g)^T = f^T \⊗ g^T.
Proof. by rewrite !trfAC tenf_adj tenf_conj. Qed.

Lemma tenf_norm S T S' T' (f: 'F[E]_(S,T)) (g: 'F_(S',T')) :
  [disjoint S & S'] -> [disjoint T & T'] ->
  `|f \⊗ g| = `|f| * `|g|.
Proof.
move=>dS dT; rewrite /Num.norm/= /trfnorm h2mx_tenf /trnorm
  schattennormUr_eq_dim ?schattennormUl_eq_dim ?schattennorm_tens// ?tenv_dim//.
by apply/tenv_mxU_adj_unitarymx. by apply/tenv_mxU_unitarymx.
Qed.

Lemma tenf_i2fnorm S T S' T' (f: 'F[E]_(S,T)) (g: 'F_(S',T')) :
  [disjoint S & S'] -> [disjoint T & T'] ->
  i2fnorm (f \⊗ g) = i2fnorm f * i2fnorm g.
Proof.
move=>dS dT; rewrite /Num.norm/= /i2fnorm h2mx_tenf  
  i2normUr_eq_dim ?i2normUl_eq_dim ?i2norm_tens// ?tenv_dim//.
by apply/tenv_mxU_adj_unitarymx. by apply/tenv_mxU_unitarymx.
Qed.

Lemma linear_dotf S T S' T' f : linear (@dot_lfun I E S T S' T' f).
Proof.
move=>a v w; rewrite dot_lfun.unlock linearPl/=.
by rewrite linearP/= comp_lfunDr comp_lfunZr.
Qed.
HB.instance Definition _ S T S' T' f := GRing.isLinear.Build C 'F[E]_(S',T')
  'F_(S' :|: S :\: T', T :|: T' :\: S) *:%R (@dot_lfun I E S T S' T' f) (@linear_dotf S T S' T' f).
Lemma linear_dotfr S T S' T' f : linear ((@dot_lfun I E S T S' T')^~ f).
Proof.
move=>a v w; rewrite dot_lfun.unlock linearPl/=.
by rewrite comp_lfunDl comp_lfunZl.
Qed.
HB.instance Definition _ S T S' T' := bilinear_isBilinear.Build C 'F[E]_(S,T) 'F[E]_(S',T')
  'F_(S' :|: S :\: T', T :|: T' :\: S) *:%R *:%R (@dot_lfun I E S T S' T') 
    (@linear_dotfr S T S' T', @linear_dotf S T S' T').

Lemma dotf_conj S T S' T' (f: 'F[E]_(S,T)) (g: 'F_(S',T')) :
  (f \· g)^C = f^C \· g^C.
Proof. by rewrite dot_lfun.unlock !conjf_comp castlf_conj !tenf_conj !conjf1. Qed.

Lemma dotf_adj S T S' T' (f: 'F[E]_(S,T)) (g: 'F_(S',T')) :
  (f \· g)^A = g^A \· f^A.
Proof.
rewrite dot_lfun.unlock !adjf_comp castlf_adj /= !tenf_adj castlf_complfl castlf_id !adjf1.
by f_equal; apply/castlf_sym; rewrite castlf_comp castlf_id. 
Qed.

Lemma dotf_tr S T S' T' (f: 'F[E]_(S,T)) (g: 'F_(S',T')) :
  (f \· g)^T = g^T \· f^T.
Proof. by rewrite !trfAC dotf_adj dotf_conj. Qed.

Lemma linear_sdotf S T f : linear (@sdot_lfun I E S T f).
Proof. by move=>a v w; rewrite sdot_lfun.unlock linearP/= linearD/= linearZ/=. Qed.
HB.instance Definition _ S T f := GRing.isLinear.Build C 'F[E]_T
  'F_(S :|: T) *:%R (@sdot_lfun I E S T f) (@linear_sdotf S T f).
Lemma linear_sdotfr S T f : linear ((@sdot_lfun I E S T)^~ f).
Proof. by move=>a v w; rewrite sdot_lfun.unlock linearPl/= linearD/= linearZ/=. Qed.
HB.instance Definition _ S T := bilinear_isBilinear.Build C 'F[E]_S 'F[E]_T
  'F_(S :|: T) *:%R *:%R (@sdot_lfun I E S T) (@linear_sdotfr S T, @linear_sdotf S T).

Lemma sdotf_conj S T (f: 'F[E]_S) (g: 'F_T) :
  (f \O g)^C = f^C \O g^C.
Proof. by rewrite sdot_lfun.unlock castlf_conj dotf_conj. Qed.

Lemma intro_dvf S T W (f: 'F[E]_(T, W)) (g: 'F[E]_(S,T)) u :
  f (g u) = \sum_i cdv i (g u) *: f (deltav i).
Proof.
rewrite {1}(dec_dv (g u)) linear_sum /=.
by apply eq_bigr=>i _; rewrite linearZ.
Qed.

Lemma tenf_castA S1 T1 S2 T2 S3 T3 (f: 'F[E]_(S1,T1)) (g: 'F_(S2,T2))
  (h: 'F_(S3,T3)) : 
 castlf (setUA S1 S2 S3, setUA T1 T2 T3) (f \⊗ (g \⊗ h)) = ((f \⊗ g) \⊗ h).
Proof.
apply/lfunPD=>/=i. apply/cdvP=>/= j.
rewrite castlfE/= cdv_castV deltav_cast -!tenf_dv !cdvT mulrA.
do ? [apply f_equal2 | apply f_equal] =>//; 
rewrite ?idxSl_idxR ?idxSr_idxR ?idxR_castR -?setUA ?subsetUl ?subsetUr// => H1; 
rewrite !idxRA; by do ? [apply f_equal2 | apply eq_irrelevance].
Qed.

Lemma tenf_castC S T S' T' (f: 'F[E]_(S,T)) (g: 'F_(S',T')) : 
  castlf ((setUC S S'), (setUC T T')) (f \⊗ g) = (g \⊗ f).
Proof.
apply/lfunPD=>/=i. apply/cdvP=>/= j.
rewrite castlfE/= deltav_cast cdv_castV -!tenf_dv !cdvT mulrC.
do ? [apply f_equal2 | apply f_equal] =>//; 
    rewrite ?idxS_idxR ?idxR_cast ?subsetUl ?subsetUr// => H1;
    by do ? [apply f_equal2 | apply eq_irrelevance].
Qed.

Lemma tenf_cast1r S T (f: 'F[E]_(S,T))  : 
  castlf ((setU0 S),(setU0 T)) (f \⊗ (\1 : 'F_set0)) = f.
Proof.
apply/lfunPD=>/=i; rewrite castlfE deltav_cast/= -tenf_dv idx0E castidxs0.
by rewrite castidx_comp castidx_id lfunE/= tenv_idx0r casths_comp casths_id.
Qed.

Lemma tenf_v2f S T (u : 'H[E]_S) (v : 'H_T) :
  castlf (setU0 _, erefl) (ten_lfun (v2f u) (v2f v)) = (v2f (tenv u v)).
Proof.
by apply/lfunPD=>i; rewrite castlfE/= deltav_cast -tenf_dv 
  !idx0E /v2f !outpE dv_dot eqxx !scale1r.
Qed.

Lemma tenv_v2f S T (u : 'H[E]_S) (v : 'H_T) :
  castlf (esym (setU0 _), erefl) (v2f (tenv u v)) = (ten_lfun (v2f u) (v2f v)).
Proof. by rewrite -tenf_v2f castlf_comp castlf_id. Qed.

Lemma tenf_v2df S T (u : 'H[E]_S) (v : 'H_T) :
  castlf (erefl, setU0 _) (ten_lfun (v2df u) (v2df v)) = (v2df (tenv u v)).
Proof. by rewrite -!v2f_adj -tenf_v2f castlf_adj/= tenf_adj. Qed.

Lemma tenv_v2df S T (u : 'H[E]_S) (v : 'H_T) :
  castlf (erefl, esym (setU0 _)) (v2df (tenv u v)) = (ten_lfun (v2df u) (v2df v)).
Proof. by rewrite -tenf_v2df castlf_comp castlf_id. Qed.

Lemma tenf_f2v S T (u : 'FV[E]_S) (v : 'FV_T) :
  f2v (castlf (setU0 _, erefl) (ten_lfun u v)) = tenv (f2v u) (f2v v).
Proof. by rewrite -{1}[u]f2vK -{1}[v]f2vK -tenv_v2f castlf_comp castlf_id v2fK. Qed.

Lemma tenv_f2v S T (u : 'FV[E]_S) (v : 'FV_T) :
  castlf (esym (setU0 _), erefl) (v2f (tenv (f2v u) (f2v v))) = (ten_lfun u v).
Proof. by rewrite -tenf_f2v f2vK castlf_comp castlf_id. Qed.

Lemma tenf_df2v S T (u : 'FdV[E]_S) (v : 'FdV_T) :
  df2v (castlf (erefl, setU0 _) (ten_lfun u v)) = tenv (df2v u) (df2v v).
Proof. by rewrite -!f2v_adj -tenf_f2v castlf_adj tenf_adj. Qed.

Lemma tenv_df2v S T (u : 'FdV[E]_S) (v : 'FdV_T) :
  castlf (erefl, esym (setU0 _)) (v2df (tenv (df2v u) (df2v v))) = (ten_lfun u v).
Proof. by rewrite -tenf_df2v df2vK castlf_comp castlf_id. Qed.

Lemma tenfmdv (J: finType) (fs fs' : J -> {set I}) 
  (f: forall i : J, 'F[E]_(fs i, fs' i)) (i : idx _ (\bigcup_i (fs i))) :
    tenfm f (deltav i)
      = tenvm (fun k : J => f k (deltav (flatidx i k))).
Proof.
rewrite tenfm.unlock injectf_delta tenvm.unlock; f_equal.
by apply/mvectorP=>j; rewrite !mvE.
Qed.

Lemma tenfmP (J: finType) (fs fs' : J -> {set I}) (f g : forall i : J, 'F[E]_(fs i, fs' i)) :
  (forall i, f i = g i) -> tenfm f = tenfm g.
Proof. by move=>P; apply/lfunPD=>i; rewrite !tenfmdv; apply/tenvmP=>j; rewrite P. Qed.

Lemma tenfm_apply (J: finType) (fs fs' : J -> {set I}) 
  (f: forall i : J, 'F[E]_(fs i, fs' i)) (v : forall i : J, 'H_(fs i)) :
    disf fs ->
    tenfm f (tenvm v) = tenvm (fun k : J => f k (v k)).
Proof.
move=>dis; rewrite tenfm.unlock tenvm.unlock injectfE//; f_equal.
by apply/mvectorP=>j; rewrite !mvE.
Qed.

Lemma tenfm_outp (J: finType) (fs fs' : J -> {set I}) 
  (u : forall i : J, 'H[E]_(fs i)) (v : forall i : J, 'H_(fs' i)) :
  tenfm (fun k : J => [> u k ; v k <]) = [> tenvm u ; tenvm v <].
Proof.
apply/lfunPD=>i. rewrite tenfmdv outpE. apply/intro_cdvl=>j.
rewrite linearZ/= -conj_dotp -cdvE !cdv_tm rmorph_prod -big_split/=.
by apply eq_bigr=>k _; rewrite outpE linearZ/= !cdvE conj_dotp.
Qed.

Lemma tenfm_adj (J: finType) (fs fs' : J -> {set I}) 
  (f: forall i : J, 'F[E]_(fs i, fs' i)) :
    (tenfm f)^A = tenfm (fun i=>(f i)^A).
Proof.
apply/lfunPD=>i; apply/cdvP=>j; rewrite adj_cdv !tenfmdv !cdv_tm rmorph_prod.
by apply eq_bigr=>k _; rewrite adj_cdv.
Qed.

Lemma tenfm_conj (J: finType) (fs fs' : J -> {set I}) 
  (f: forall i : J, 'F[E]_(fs i, fs' i)) :
    (tenfm f)^C = tenfm (fun i=>(f i)^C).
Proof.
apply/lfunPD=>i; apply/cdvP=>j.
rewrite conjfE conj_cdv conj_dv !tenfmdv !cdv_tm rmorph_prod.
by apply eq_bigr=>k _; rewrite conjfE conj_dv conj_cdv.
Qed.

Lemma tenfm_tr (J: finType) (fs fs' : J -> {set I}) 
  (f: forall i : J, 'F[E]_(fs i, fs' i)) :
    (tenfm f)^T = tenfm (fun i=>(f i)^T).
Proof. by rewrite trfAC tenfm_adj tenfm_conj; apply/tenfmP=>i; rewrite trfAC. Qed.

Lemma tenfm_recl (n : nat) (dt dt' : n.+1.-tuple {set I}) 
  (f: forall i : 'I_n.+1, 'F[E]_(dt ~_ i, dt' ~_ i)) :
  castlf (esym (idx_big_recl_cast dt), esym (idx_big_recl_cast dt')) (tenfm f) = 
    (f ord0 \⊗ tenfm (fun i=> (f (fintype.lift ord0 i)))).
Proof.
apply/lfunPD=>i; apply/cdvP=>j; rewrite castlfE/= esymK -cdv_cast 
  deltav_cast tenfmdv cdv_tm -tenf_dv cdvT tenfmdv cdv_tm.
rewrite big_ord_recl !idx_big_recl0 !castidx_comp !castidx_id; f_equal.
apply eq_bigr=>/= k _; do ? f_equal;
by rewrite -idx_big_recl castidx_comp castidx_id.
Qed.

Lemma tenfmZ (J: finType) (fs fs' : J -> {set I}) (a : forall i : J, C) 
  (x: forall i : J, 'F[E]_(fs i, fs' i)) :
    (tenfm (fun i => a i *: x i)) = (\prod_i a i) *: tenfm x.
Proof.
rewrite tenfm.unlock -mlinearZm. exact: injectf_mlinear.
by f_equal; apply/mvectorP=>i; rewrite !mvE.
Qed.

Lemma tenfm_sum (J: finType) (fs fs': J -> {set I}) (K : J -> finType)
  (x: forall i : J, (K i) -> 'F[E]_(fs i, fs' i)) :
    (tenfm (fun i => \sum_j x i j)) = 
      \sum_(b : mvector (fun i : J => (K i))) tenfm (fun i => x i (b i)).
Proof. by rewrite tenfm.unlock (mlinear_sum x (@injectf_mlinear _ _ _ _ _)). Qed.

End LinfunDef.

Section TenDotTheory.
Context (I : finType) (E : I -> chsType).
Variables (S T S' T' : {set I}).
Implicit Type (f: 'F[E]_(S,T)) (g: 'F[E]_(S',T')).

Lemma tenf0 f : f \⊗ (0: 'F_(S',T')) = 0.
Proof. exact: linear0r. Qed.

Lemma ten0f g : (0: 'F_(S,T)) \⊗ g = 0.
Proof. exact: linear0l. Qed.

Lemma tenf11 : (\1: 'F[E]_S) \⊗ (\1: 'F_S') = \1.
Proof.
apply/lfunPD=>i; rewrite lfunE/= ten_lfun_fun.unlock (bigD1 i)//= big1.
by move=>k /negPf nki; rewrite cdv_dv nki scale0r.
by rewrite !lfunE /= -dv_split cdv_dv eqxx scale1r addr0.
Qed.

Lemma tenfDl g (f1 f2: 'F_(S,T)) : (f1 + f2) \⊗ g = (f1 \⊗ g) + (f2 \⊗ g).
Proof. exact: linearDl. Qed.

Lemma tenfDr f (g1 g2: 'F_(S',T')) : f \⊗ (g1 + g2) = (f \⊗ g1) + (f \⊗ g2).
Proof. exact: linearDr. Qed.

Lemma tenfNl g f : (- f) \⊗ g = - (f \⊗ g).
Proof. exact: linearNl. Qed.

Lemma tenfNr f g : f \⊗ (- g) = - (f \⊗ g).
Proof. exact: linearNr. Qed.

Lemma tenfZl g (c: C) f : (c *: f) \⊗ g = c *: (f \⊗ g).
Proof. exact: linearZl_LR. Qed.

Lemma tenfZr f (c: C) g : f \⊗ (c *: g) = c *: (f \⊗ g).
Proof. exact: linearZr. Qed.

Lemma tenfBl g f1 f2 : (f1 - f2) \⊗ g = f1 \⊗ g - f2 \⊗ g.
Proof. exact: linearBl. Qed.

Lemma tenfBr f g1 g2 : f \⊗ (g1 - g2) = f \⊗ g1 - f \⊗ g2.
Proof. exact: linearBr. Qed.

Lemma tenfPl g (c: C) f1 f2: (c *: f1 + f2) \⊗ g = c *: (f1 \⊗ g) + (f2 \⊗ g).
Proof. exact: linearPl. Qed.

Lemma tenfPr f (c: C) g1 g2 : f \⊗ (c *: g1 + g2) = c *: (f \⊗ g1) + (f \⊗ g2).
Proof. exact: linearPr. Qed.

Lemma tenfMnl g f n : (f *+ n) \⊗ g = (f \⊗ g) *+ n.
Proof. exact: linearMnl. Qed.

Lemma tenfMnr f g n : f \⊗ (g *+ n) = (f \⊗ g) *+ n.
Proof. exact: linearMnr. Qed.

Lemma tenfMNnl g f n : (f *- n) \⊗ g = (f \⊗ g) *- n.
Proof. exact: linearMNnl. Qed.

Lemma tenfMNnr f g n : f \⊗ (g *- n) = (f \⊗ g) *- n.
Proof. exact: linearMNnr. Qed.

Lemma tenf_suml g J r (P: pred J) (F: J -> 'F[E]_(S, T)) :
 (\sum_(i <- r | P i) F i) \⊗ g = \sum_(i <- r | P i) (F i \⊗ g).
Proof. exact: linear_suml. Qed.

Lemma tenf_sumr f J r (P: pred J) (F: J -> 'F[E]_(S', T')) :
 f \⊗ (\sum_(i <- r | P i) F i) = \sum_(i <- r | P i) (f \⊗ F i).
Proof. exact: linear_sumr. Qed.

Lemma tenf_comp1r W f (h: 'F_(W,S)) : [disjoint S & S'] -> 
  (f \o h) \⊗ (\1: 'F_S') = (f \⊗ \1) \o (h \⊗ \1).
Proof. by move=>dis; rewrite -tenf_comp// comp_lfun1l. Qed.

Lemma tenf_comp1l W f (h: 'F_(W,S)) : [disjoint S' & S] -> 
  (\1: 'F_S') \⊗ (f \o h) = (\1 \⊗ f) \o (\1 \⊗ h).
Proof. by move=>dis; rewrite -tenf_comp// comp_lfun1l. Qed.

Lemma dotf0 f : f \· (0: 'F_(S',T')) = 0.
Proof. exact: linear0r. Qed.

Lemma dot0f g : (0: 'F_(S,T)) \· g = 0.
Proof. exact: linear0l. Qed.

Lemma dotfDl g f1 f2 : (f1 + f2) \· g = f1 \· g + f2 \· g.
Proof. exact: linearDl. Qed. 

Lemma dotfDr f g1 g2 : f \· (g1 + g2) = f \· g1 + f \· g2.
Proof. exact: linearDr. Qed. 

Lemma dotfNl g f : (- f) \· g = - (f \· g).
Proof. exact: linearNl. Qed. 

Lemma dotfNr f g : f \· (- g) = - (f \· g).
Proof. exact: linearNr. Qed. 

Lemma dotfZl g c f : (c *: f) \· g = c *: (f \· g).
Proof. exact: linearZl_LR. Qed. 

Lemma dotfZr f c g : f \· (c *: g) = c *: (f \· g).
Proof. exact: linearZr. Qed. 

Lemma dotfBl g f1 f2 : (f1 - f2) \· g = f1 \· g - f2 \· g.
Proof. exact: linearBl. Qed. 

Lemma dotfBr f g1 g2 : f \· (g1 - g2) = f \· g1 - f \· g2.
Proof. exact: linearBr. Qed. 

Lemma dotfPl g c f1 f2 : (c *: f1 + f2) \· g = c *: (f1 \· g) + (f2 \· g).
Proof. exact: linearPl. Qed. 

Lemma dotfPr f c g1 g2 : f \· (c *: g1 + g2) = c *: (f \· g1) + (f \· g2).
Proof. exact: linearPr. Qed. 

Lemma dotfMnl g f n : (f *+ n) \· g = (f \· g) *+ n.
Proof. exact: linearMnl. Qed.

Lemma dotfMnr f g n : f \· (g *+ n) = (f \· g) *+ n.
Proof. exact: linearMnr. Qed.

Lemma dotfMNnl g f n : (f *- n) \· g = (f \· g) *- n.
Proof. exact: linearMNnl. Qed.

Lemma dotfMNnr f g n : f \· (g *- n) = (f \· g) *- n.
Proof. exact: linearMNnr. Qed.

Lemma dotf_suml g J r (P: pred J) (F: J -> 'F_(S, T)) :
 (\sum_(i <- r | P i) F i) \· g = \sum_(i <- r | P i) ((F i) \· g).
Proof. exact: linear_suml. Qed.

Lemma dotf_sumr f J r (P: pred J) (F: J -> 'F_(S', T')) :
  f \· (\sum_(i <- r | P i) F i) = \sum_(i <- r | P i) (f \· (F i)).
Proof. exact: linear_sumr. Qed.

End TenDotTheory.

Section SdotTheory.
Context (I : finType) (E : I -> chsType).
Variables (S T : {set I}).
Implicit Type (f: 'F[E]_S) (g: 'F[E]_T).

Lemma sdotf0 f : f \O (0: 'F_T) = 0.
Proof. exact: linear0r. Qed.

Lemma sdot0f g : (0: 'F_S) \O g = 0.
Proof. exact: linear0l. Qed.

Lemma sdotf11 : (\1 : 'F[E]_S) \O (\1 : 'F_T) = \1.
Proof.
rewrite sdot_lfun.unlock dot_lfun.unlock !tenf11 comp_lfun1l castlf_comp etrans_id.
by rewrite (eq_irrelevance (etrans _ _) (setUDV T S)) castlf1.
Qed.

Lemma sdotfDl g f1 f2 : (f1 + f2) \O g = f1 \O g + f2 \O g.
Proof. exact: linearDl. Qed. 

Lemma sdotfDr f g1 g2 : f \O (g1 + g2) = f \O g1 + f \O g2.
Proof. exact: linearDr. Qed. 

Lemma sdotfNl g f : (- f) \O g = - (f \O g).
Proof. exact: linearNl. Qed. 

Lemma sdotfNr f g : f \O (- g) = - (f \O g).
Proof. exact: linearNr. Qed. 

Lemma sdotfZl g c f : (c *: f) \O g = c *: (f \O g).
Proof. exact: linearZl_LR. Qed. 

Lemma sdotfZr f c g : f \O (c *: g) = c *: (f \O g).
Proof. exact: linearZr. Qed. 

Lemma sdotfBl g f1 f2 : (f1 - f2) \O g = f1 \O g - f2 \O g.
Proof. exact: linearBl. Qed. 

Lemma sdotfBr f g1 g2 : f \O (g1 - g2) = f \O g1 - f \O g2.
Proof. exact: linearBr. Qed. 

Lemma sdotfPl g c f1 f2 : (c *: f1 + f2) \O g = c *: (f1 \O g) + (f2 \O g).
Proof. exact: linearPl. Qed. 

Lemma sdotfPr f c g1 g2 : f \O (c *: g1 + g2) = c *: (f \O g1) + (f \O g2).
Proof. exact: linearPr. Qed. 

Lemma sdotfMnl g f n : (f *+ n) \O g = (f \O g) *+ n.
Proof. exact: linearMnl. Qed.

Lemma sdotfMnr f g n : f \O (g *+ n) = (f \O g) *+ n.
Proof. exact: linearMnr. Qed.

Lemma sdotfMNnl g f n : (f *- n) \O g = (f \O g) *- n.
Proof. exact: linearMNnl. Qed.

Lemma sdotfMNnr f g n : f \O (g *- n) = (f \O g) *- n.
Proof. exact: linearMNnr. Qed.

Lemma sdotf_suml g J r (P: pred J) (F: J -> 'F_S) :
 (\sum_(i <- r | P i) F i) \O g = \sum_(i <- r | P i) ((F i) \O g).
Proof. exact: linear_suml. Qed.

Lemma sdotf_sumr f J r (P: pred J) (F: J -> 'F_T) :
  f \O (\sum_(i <- r | P i) F i) = \sum_(i <- r | P i) (f \O (F i)).
Proof. exact: linear_sumr. Qed.

End SdotTheory.

Section NonDepDef.
Context (I : finType) (H : I -> chsType).
Implicit Type (A B : {set I}).

Inductive Hnd := HND (A : {set I}) & 'H[H]_A.
Definition to_Hnd A (v : 'H[H]_A) := HND v.
Coercion to_Hnd : CanonicalHermitianSpace.sort >-> Hnd.
Definition vdom (x : Hnd) := let: HND x _ := x in x.
Definition of_Hnd (x : Hnd) : 'H[H]_(vdom x) :=
  let: HND _ x := x in x.
Coercion of_Hnd : Hnd >-> CanonicalHermitianSpace.sort.

Definition Hnd_conj (x : Hnd) : Hnd := to_Hnd ((of_Hnd x)^*v).
Definition Hnd_ten (x y : Hnd) : Hnd := (of_Hnd x) ⊗v (of_Hnd y).

Inductive Fnd := FND (A B : {set I}) & 'F[H]_(A,B).
Definition to_Fnd A B (f : 'F[H]_(A,B)) := FND f.
Coercion to_Fnd : hom >-> Fnd.
Definition tdom (x : Fnd) := let: FND x _ _ := x in x. 
Definition tcdom (x : Fnd) := let: FND _ x _ := x in x. 
Definition of_Fnd (x : Fnd) : 'F[H]_(tdom x, tcdom x) := 
  let: FND _ _ f := x in f.
Coercion of_Fnd : Fnd >-> hom.

Definition Fnd_adj (x : Fnd) : Fnd := x^A.
Definition Fnd_conj (x : Fnd) : Fnd := x^C.
Definition Fnd_tr (x : Fnd) : Fnd := x^T.
Definition Fnd_scale (c : C) (x : Fnd) : Fnd := c *: (of_Fnd x).
Definition Fnd_opp (x : Fnd) : Fnd := - (of_Fnd x).
Definition Fnd_dot (x y : Fnd) : Fnd := (of_Fnd x) \· (of_Fnd y).
Definition Fnd_ten (x y : Fnd) : Fnd := (of_Fnd x) \⊗ (of_Fnd y).

End NonDepDef.

Declare Scope efnd_scope.
Delimit Scope efnd_scope with EFND.
Declare Scope fnd_scope.
Delimit Scope fnd_scope with FND.
Bind Scope fnd_scope with Fnd.

Notation "X %:Hnd" := (to_Hnd X%VF) (at level 2, left associativity, only parsing).
Notation "X %:Fnd" := (to_Fnd X%VF) (at level 2, left associativity, only parsing).
Notation "X '=v' Y" := (to_Hnd X%VF = to_Hnd Y%VF) (at level 70) : efnd_scope.
Notation "X '=c' Y" := (to_Fnd X%VF = to_Fnd Y%VF) (at level 70) : efnd_scope.
Notation "x '^*v'" := (Hnd_conj x) : fnd_scope.
Notation "x ⊗v y" := (Hnd_ten x y) : fnd_scope.
Notation "f \⊗ g" := (Fnd_ten f g) : fnd_scope.
Notation "f \· g" := (Fnd_dot f g) : fnd_scope.
Notation "f ^A" := (Fnd_adj f) : fnd_scope.
Notation "f ^C" := (Fnd_conj f) : fnd_scope.
Notation "f ^T" := (Fnd_tr f) : fnd_scope.
Notation "c *: f" := (Fnd_scale c f) : fnd_scope.
Notation "- f" := (Fnd_opp f) : fnd_scope.
Reserved Notation "\tenv_ i F"
  (at level 36, F at level 36, i at level 0,
           format "'[' \tenv_ i '/  '  F ']'").
Reserved Notation "\tenv_ ( i <- r | P ) F"
  (at level 36, F at level 36, i, r at level 50,
           format "'[' \tenv_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\tenv_ ( i <- r ) F"
  (at level 36, F at level 36, i, r at level 50,
           format "'[' \tenv_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\tenv_ ( m <= i < n | P ) F"
  (at level 36, F at level 36, i, m, n at level 50,
           format "'[' \tenv_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\tenv_ ( m <= i < n ) F"
  (at level 36, F at level 36, i, m, n at level 50,
           format "'[' \tenv_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\tenv_ ( i | P ) F"
  (at level 36, F at level 36, i at level 50,
           format "'[' \tenv_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\tenv_ ( i : t | P ) F"
  (at level 36, F at level 36, i at level 50). (* only parsing *)
Reserved Notation "\tenv_ ( i : t ) F"
  (at level 36, F at level 36, i at level 50). (* only parsing *)
Reserved Notation "\tenv_ ( i < n | P ) F"
  (at level 36, F at level 36, i, n at level 50,
           format "'[' \tenv_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\tenv_ ( i < n ) F"
  (at level 36, F at level 36, i, n at level 50,
           format "'[' \tenv_ ( i  <  n ) '/  '  F ']'").
Reserved Notation "\tenv_ ( i 'in' A | P ) F"
  (at level 36, F at level 36, i, A at level 50,
           format "'[' \tenv_ ( i  'in'  A  |  P )  F ']'").
Reserved Notation "\tenv_ ( i 'in' A ) F"
  (at level 36, F at level 36, i, A at level 50,
           format "'[' \tenv_ ( i  'in'  A ) '/  '  F ']'").

Reserved Notation "\tenf_ i F"
  (at level 36, F at level 36, i at level 0,
           format "'[' \tenf_ i '/  '  F ']'").
Reserved Notation "\tenf_ ( i <- r | P ) F"
  (at level 36, F at level 36, i, r at level 50,
           format "'[' \tenf_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\tenf_ ( i <- r ) F"
  (at level 36, F at level 36, i, r at level 50,
           format "'[' \tenf_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\tenf_ ( m <= i < n | P ) F"
  (at level 36, F at level 36, i, m, n at level 50,
           format "'[' \tenf_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\tenf_ ( m <= i < n ) F"
  (at level 36, F at level 36, i, m, n at level 50,
           format "'[' \tenf_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\tenf_ ( i | P ) F"
  (at level 36, F at level 36, i at level 50,
           format "'[' \tenf_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\tenf_ ( i : t | P ) F"
  (at level 36, F at level 36, i at level 50). (* only parsing *)
Reserved Notation "\tenf_ ( i : t ) F"
  (at level 36, F at level 36, i at level 50). (* only parsing *)
Reserved Notation "\tenf_ ( i < n | P ) F"
  (at level 36, F at level 36, i, n at level 50,
           format "'[' \tenf_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\tenf_ ( i < n ) F"
  (at level 36, F at level 36, i, n at level 50,
           format "'[' \tenf_ ( i  <  n ) '/  '  F ']'").
Reserved Notation "\tenf_ ( i 'in' A | P ) F"
  (at level 36, F at level 36, i, A at level 50,
           format "'[' \tenf_ ( i  'in'  A  |  P )  F ']'").
Reserved Notation "\tenf_ ( i 'in' A ) F"
  (at level 36, F at level 36, i, A at level 50,
           format "'[' \tenf_ ( i  'in'  A ) '/  '  F ']'").

Notation "\tenv_ ( i <- r | P ) F" :=
  (\big[ @Hnd_ten _ _ / to_Hnd (deltav idx0) ]_(i <- r | P%B) F%FND ) : fnd_scope.
Notation "\tenv_ ( i <- r ) F" :=
  (\big[ @Hnd_ten _ _ / to_Hnd (deltav idx0) ]_(i <- r) F%FND) : fnd_scope.
Notation "\tenv_ ( m <= i < n | P ) F" :=
  ((\big[ @Hnd_ten _ _ / to_Hnd (deltav idx0) ]_( m%N <= i < n%N | P%B) F%FND)%BIG) 
    : fnd_scope.
Notation "\tenv_ ( m <= i < n ) F" :=
  ((\big[ @Hnd_ten _ _ / to_Hnd (deltav idx0) ]_(m%N <= i < n%N) F%FND)%BIG) : fnd_scope.
Notation "\tenv_ ( i | P ) F" :=
  (\big[ @Hnd_ten _ _ / to_Hnd (deltav idx0) ]_(i | P%B) F%FND) : fnd_scope.
Notation "\tenv_ i F" :=
  (\big[ @Hnd_ten _ _ / to_Hnd (deltav idx0) ]_i F%FND) : fnd_scope.
Notation "\tenv_ ( i : t | P ) F" :=
  (\big[ @Hnd_ten _ _ / to_Hnd (deltav idx0) ]_(i : t | P%B) F%FND) (only parsing) 
    : fnd_scope.
Notation "\tenv_ ( i : t ) F" :=
  (\big[ @Hnd_ten _ _ / to_Hnd (deltav idx0) ]_(i : t) F%FND) (only parsing) : fnd_scope.
Notation "\tenv_ ( i < n | P ) F" :=
  ((\big[ @Hnd_ten _ _ / to_Hnd (deltav idx0) ]_(i < n%N | P%B) F%FND)%BIG) : fnd_scope.
Notation "\tenv_ ( i < n ) F" :=
  ((\big[ @Hnd_ten _ _ / to_Hnd (deltav idx0) ]_(i < n%N) F%FND)%BIG) : fnd_scope.
Notation "\tenv_ ( i 'in' A | P ) F" :=
  (\big[ @Hnd_ten _ _ / to_Hnd (deltav idx0) ]_(i in A | P%B) F%FND) : fnd_scope.
Notation "\tenv_ ( i 'in' A ) F" :=
  (\big[ @Hnd_ten _ _ / to_Hnd (deltav idx0) ]_(i in A) F%FND) : fnd_scope.

Definition Fnd1 (I : finType) (H : I -> chsType) := to_Fnd (\1 : 'F[H]_set0).
Arguments Fnd1 {I H}.

Notation "\tenf_ ( i <- r | P ) F" :=
  (\big[ @Fnd_ten _ _ / Fnd1 ]_(i <- r | P%B) F%FND ) : fnd_scope.
Notation "\tenf_ ( i <- r ) F" :=
  (\big[ @Fnd_ten _ _ / Fnd1 ]_(i <- r) F%FND) : fnd_scope.
Notation "\tenf_ ( m <= i < n | P ) F" :=
  ((\big[ @Fnd_ten _ _ / Fnd1 ]_( m%N <= i < n%N | P%B) F%FND)%BIG) 
    : fnd_scope.
Notation "\tenf_ ( m <= i < n ) F" :=
  ((\big[ @Fnd_ten _ _ / Fnd1 ]_(m%N <= i < n%N) F%FND)%BIG) : fnd_scope.
Notation "\tenf_ ( i | P ) F" :=
  (\big[ @Fnd_ten _ _ / Fnd1 ]_(i | P%B) F%FND) : fnd_scope.
Notation "\tenf_ i F" :=
  (\big[ @Fnd_ten _ _ / Fnd1 ]_i F%FND) : fnd_scope.
Notation "\tenf_ ( i : t | P ) F" :=
  (\big[ @Fnd_ten _ _ / Fnd1 ]_(i : t | P%B) F%FND) (only parsing) 
    : fnd_scope.
Notation "\tenf_ ( i : t ) F" :=
  (\big[ @Fnd_ten _ _ / Fnd1 ]_(i : t) F%FND) (only parsing) : fnd_scope.
Notation "\tenf_ ( i < n | P ) F" :=
  ((\big[ @Fnd_ten _ _ / Fnd1 ]_(i < n%N | P%B) F%FND)%BIG) : fnd_scope.
Notation "\tenf_ ( i < n ) F" :=
  ((\big[ @Fnd_ten _ _ / Fnd1 ]_(i < n%N) F%FND)%BIG) : fnd_scope.
Notation "\tenf_ ( i 'in' A | P ) F" :=
  (\big[ @Fnd_ten _ _ / Fnd1 ]_(i in A | P%B) F%FND) : fnd_scope.
Notation "\tenf_ ( i 'in' A ) F" :=
  (\big[ @Fnd_ten _ _ / Fnd1 ]_(i in A) F%FND) : fnd_scope.

Local Open Scope efnd_scope.

Section NonDepHerm.
Context {L : finType} {H : L -> chsType}.
Implicit Type (x y : Hnd H) (A B : {set L}).

Lemma to_HndK A (f : 'H[H]_A) : of_Hnd (to_Hnd f) = f.
Proof. by []. Qed.
Lemma of_HndK x : to_Hnd (of_Hnd x) = x.
Proof. by case: x. Qed.
Lemma to_Hnd_inj A : injective (@to_Hnd _ H A).
Proof. by move=>x y Pxy; inversion Pxy; move: H1=>/inj_existT. Qed.

Lemma eq_Hnd x y (Hd : vdom x = vdom y) :
  casths Hd x = y -> x = y.
Proof.
case: x Hd; case: y=> sx x sy y/= Pv; 
by case: sx / Pv x=>x; rewrite casths_id=>->.
Qed.

Lemma eq_Hnd1 x y : x = y -> vdom x = vdom y.
Proof. by move=>->. Qed.

Lemma eq_Hnd2 x y (Hd : vdom x = vdom y) :
  x = y -> casths Hd x = y.
Proof. 
case: x Hd; case: y=> sx x sy y/= Pv; 
by case: sx / Pv x=>x /to_Hnd_inj; rewrite casths_id.
Qed.

Lemma eq_HndP x y (eqxy : x = y) : casths (eq_Hnd1 eqxy) x = y.
Proof. by apply: eq_Hnd2. Qed.

Lemma Hnd_cast A1 A2 (eqA : A1 = A2) (x : 'H[H]_ _) :
  to_Hnd (casths eqA x) = x.
Proof. by case: A2 / eqA. Qed.

Lemma to_Hnd_conjE A (f : 'H[H]_A) :
  to_Hnd (f^*v) = Hnd_conj f.
Proof. by []. Qed.
Lemma to_Hnd_tenE A1 A2 (f1 : 'H[H]_A1) (f2 : 'H[H]_A2) :
  to_Hnd (f1 ⊗v f2) = Hnd_ten f1 f2.
Proof. by []. Qed.

Lemma Hnd_eq0 A1 A2 :
  A1 = A2 -> to_Hnd (0 : 'H[H]_A1) = (0 : 'H[H]_A2).
Proof. by move=>P; case: A2 / P. Qed.

Lemma of_Hnd_conjE x : of_Hnd (x^*v)%FND = (of_Hnd x)^*v.
Proof. by []. Qed.
Lemma of_Hnd_tenE x1 x2 :
  of_Hnd (x1 ⊗v x2)%FND = (of_Hnd x1) ⊗v (of_Hnd x2).
Proof. by []. Qed.

Definition of_HndE := (of_Hnd_conjE, of_Hnd_tenE).
Definition to_HndE := (to_Hnd_conjE, to_Hnd_tenE).

Lemma tenVC : commutative (@Hnd_ten _ H).
Proof. by move=>[A v1][B v2]; rewrite -!to_HndE -tenv_castC Hnd_cast. Qed.
Lemma tenVA : associative (@Hnd_ten _ H).
Proof. by move=>[A1 v1][A2 v2][A3 v3]; rewrite -!to_HndE -tenv_castA Hnd_cast. Qed.
Lemma tenV1 : right_id (to_Hnd (deltav idx0)) (@Hnd_ten _ H).
Proof. by move=>[A v]; rewrite -to_HndE tenv_idx0r Hnd_cast. Qed.
Lemma ten1V : left_id (to_Hnd (deltav idx0)) (@Hnd_ten _ H).
Proof. by move=>v; rewrite tenVC tenV1. Qed.
HB.instance Definition _ := Monoid.isComLaw.Build _ _ (@Hnd_ten _ H) tenVA tenVC ten1V.

Lemma tenvm_bij_cast (F G : finType) (f : G -> F) (bf : bijective f) 
  (dt : F -> {set L}) :
    \bigcup_j (dt (f j)) = \bigcup_i (dt i).
Proof. by rewrite (reindex f)//; move: bf=>[g fK gK]; exists g=>i _; rewrite ?fK ?gK. Qed.

Lemma incl_cast (B C : {set L}) (eqBC : B = C) : B :<=: C.
Proof. by case: C / eqBC. Qed.

Lemma incl_comp (A B C : {set L}) (p1 : A :<=: B) (p2 : B :<=: C)
  (i : 'Idx[H]_C) (j : {i : L | i \in A}) :
  i (incl p2 (incl p1 j)) = i (incl (subset_trans p1 p2) j).
Proof.
by rewrite /incl/= (eq_irrelevance  (subsetP p2 _ _)
(subsetP (subset_trans p1 p2) _ (ssrfun.svalP j))).
Qed.

Lemma idx_incl_id2 (A B : {set L}) (p1 p2 : A :<=: B) (i : 'Idx[H]_B) 
  (j : {i : L | i \in A}) : i (incl p1 j) = i (incl p2 j).
Proof. by rewrite (eq_irrelevance p1 p2). Qed.

Lemma idx_incl_id1 (B : {set L}) (p1 : B :<=: B) (i : 'Idx[H]_B) 
  (j : {i : L | i \in B}) : i (incl p1 j) = i j.
Proof. by case: j=>x p; rewrite /incl (eq_irrelevance  (subsetP p1 _ _) p). Qed.

Lemma castidxE (B C : {set L}) (eqBC : B = C) (i : 'Idx[H]_B) (j : {i : L | i \in C}) :
  castidx eqBC i j = i (incl (incl_cast (esym eqBC)) j).
Proof. by case: C / eqBC j=>j; rewrite castidx_id; symmetry; exact: idx_incl_id1. Qed.

Lemma tenvm_bij (F G : finType) (f : G -> F) (bf : bijective f) 
  (dt : F -> {set L})  (u : forall i : F, 'H[H]_(dt i)) :
    tenvm u = casths (tenvm_bij_cast bf dt) (tenvm (fun i => u (f i))).
Proof.
apply/cdvP=>i; rewrite cdv_tm cdv_castV cdv_tm; move: bf=>[g fK gK].
rewrite (reindex f); first by exists g=>j _; rewrite ?fK ?gK.
apply eq_bigr=>j _; f_equal.
rewrite /flatidx !ffunE; apply/idxP=>k.
rewrite !idxE castidxE incl_comp; exact: idx_incl_id2.
Qed.

Lemma eq_bigcup_cast (F : finType) (s t : F -> {set L}) :
  (forall i, s i = t i) -> \bigcup_i (s i) = \bigcup_i (t i).
Proof. by move=>P; under eq_bigr do rewrite P. Qed.

Lemma tenvm_cast (F : finType) (s t : F -> {set L}) (PC : forall i, s i = t i) 
  (u : forall i, 'H[H]_(s i)) :
    tenvm (fun i => casths (PC i) (u i)) = casths (eq_bigcup_cast PC) (tenvm u).
Proof.
move: PC {+}PC u => /funext -> PC u; rewrite casths_id.
by under [X in tenvm X]functional_extensionality_dep do rewrite casths_id.
Qed.

Lemma to_Hnd_tens (J : finType) (s : J -> {set L}) (v : forall j : J, 'H[H]_(s j)) :
  to_Hnd (tenvm v) = (\tenv_(j : J) (to_Hnd (v j)))%FND.
Proof.
pose h := (fun i : 'I_#|J| => enum_val i).
have bf : bijective h.
  by exists enum_rank; [ exact: enum_valK | exact: enum_rankK ] .
rewrite (tenvm_bij bf) Hnd_cast.
rewrite (reindex h)/=.
  exists enum_rank=>? _; by [rewrite enum_valK | rewrite /h enum_rankK].
set su := [tuple i => s (h i)].
have PC i : su ~_ i = s (h i) by rewrite tnthE.
set u := (fun i => casths (esym (PC i)) (v (h i)) : 'H_(su ~_ i)).
have PE i : v (h i) = casths (PC i) (u i) by rewrite /u casths_comp casths_id.
under [RHS]eq_bigr do rewrite PE Hnd_cast.
under [X in tenvm X]functional_extensionality_dep do rewrite PE.
rewrite tenvm_cast Hnd_cast.
move: su {PC} u {PE}; clear; set n := #|J|; move: n.
elim.
  move=>su u. rewrite [RHS]big_ord0. 
  have P0 : set0 = \bigcup_i (su ~_ i) by rewrite big_ord0.
  suff ->: tenvm u = casths P0 (deltav idx0) by rewrite Hnd_cast.
  by apply/cdvP=>i; rewrite cdv_tm big_ord0 cdv_castV idx0E cdv_dv eqxx.
move=>n IH su; case/tupleP: su=>s su u.
move: (tenvm_recl u)=>/(f_equal (@to_Hnd _ _ _)).
rewrite Hnd_cast=>->; rewrite to_HndE big_ord_recl; f_equal=>/=.
have PC i : su ~_ i = [tuple of s :: su] ~_ (nlift ord0 i).
  by rewrite tnthS.
pose v i := casths (esym (PC i)) (u (nlift ord0 i)).
have PE i : u (nlift ord0 i) = casths (PC i) (v i).
  by rewrite /v casths_comp casths_id.
under [RHS]eq_bigr do rewrite PE Hnd_cast.
under [X in tenvm X]functional_extensionality_dep do rewrite PE.
rewrite tenvm_cast Hnd_cast. apply: IH.
Qed.

End NonDepHerm.

Ltac to_Hnd := try (apply/to_Hnd_inj); rewrite ?(to_HndE, Hnd_cast, to_Hnd_tens).

Section NonDepLfun.
Context (I : finType) (H : I -> chsType).
Implicit Type (A B : {set I}) (x y : @Fnd _ H).

Local Open Scope fnd_scope.
Local Open Scope lfun_scope.
Local Notation Fnd := (@Fnd _ H).
Local Notation to_Fnd := (@to_Fnd _ H).

Lemma to_FndK A B (f : 'F[H]_(A,B)) : of_Fnd (to_Fnd f) = f.
Proof. by []. Qed.
Lemma of_FndK x : to_Fnd (of_Fnd x) = x.
Proof. by case: x. Qed.
Lemma to_Fnd_inj A B : injective (@to_Fnd A B).
Proof. by move=>x y Pxy; inversion Pxy; move: H1=>/inj_existT/inj_existT. Qed.

Lemma eq_Fnd x y (Hd : tdom x = tdom y) (Hcd : tcdom x = tcdom y) :
  castlf (Hd, Hcd) x = y -> x = y.
Proof.
by case: x Hd Hcd; case: y=> sx tx x sy ty y/= Pv1 Pv2; 
case: sx / Pv1 x; case: tx / Pv2=>x; rewrite castlf_id=>->.
Qed.

Lemma eq_Fnd1 x y :
  x = y -> (tdom x = tdom y) * (tcdom x = tcdom y).
Proof. by case: x; case: y=>/= x1 y1 h1 x2 y2 h2 P; inversion P. Qed.

Lemma eq_Fnd2 x y (Hd : (tdom x = tdom y) * (tcdom x = tcdom y)) :
  x = y -> castlf Hd x = y.
Proof.
by case: x Hd; case: y=> sx tx x sy ty y/= [] Pv1 Pv2; 
case: sx / Pv1 x; case: tx / Pv2=>x /to_Fnd_inj; rewrite castlf_id.
Qed.

Lemma eq_FndP x y (eqxy : x = y) : castlf (eq_Fnd1 eqxy) x = y.
Proof. by apply: eq_Fnd2. Qed.

Lemma to_Fnd_adjE A B (f : 'F[H]_(A,B)) :
  to_Fnd (f^A) = Fnd_adj f.
Proof. by []. Qed.
Lemma to_Fnd_conjE A B (f : 'F[H]_(A,B)) :
  to_Fnd (f^C) = Fnd_conj f.
Proof. by []. Qed.
Lemma to_Fnd_trE A B (f : 'F[H]_(A,B)) :
  to_Fnd (f^T) = Fnd_tr f.
Proof. by []. Qed.
Lemma to_Fnd_scaleE (c : C) A B (f : 'F[H]_(A,B)) :
  to_Fnd (c *: f) = Fnd_scale c f.
Proof. by []. Qed.
Lemma to_Fnd_oppE A B (f : 'F[H]_(A,B)) :
  to_Fnd (- f) = Fnd_opp f.
Proof. by []. Qed.
Lemma to_Fnd_dotE A1 B1 A2 B2 (f1 : 'F[H]_(A1,B1)) (f2 : 'F[H]_(A2,B2)) :
  to_Fnd (f1 \· f2) = Fnd_dot f1 f2.
Proof. by []. Qed.
Lemma to_Fnd_tenE A1 B1 A2 B2 (f1 : 'F[H]_(A1,B1)) (f2 : 'F[H]_(A2,B2)) :
  to_Fnd (f1 \⊗ f2) = Fnd_ten f1 f2.
Proof. by []. Qed.

Lemma of_Fnd_adjE x : of_Fnd (x^A) = (of_Fnd x)^A.
Proof. by []. Qed.
Lemma of_Fnd_conjE x : of_Fnd (x^C) = (of_Fnd x)^C.
Proof. by []. Qed.
Lemma of_Fnd_trE x : of_Fnd (x^T) = (of_Fnd x)^T.
Proof. by []. Qed.
Lemma of_Fnd_scaleE (c : C) x : of_Fnd (c *: x) = c *: (of_Fnd x).
Proof. by []. Qed.
Lemma of_Fnd_oppE x : of_Fnd (- x) = - (of_Fnd x).
Proof. by []. Qed.
Lemma of_Fnd_dotE x1 x2 :
  of_Fnd (x1 \· x2) = (of_Fnd x1) \· (of_Fnd x2).
Proof. by []. Qed.
Lemma of_Fnd_tenE x1 x2 :
  of_Fnd (x1 \⊗ x2) = (of_Fnd x1) \⊗ (of_Fnd x2).
Proof. by []. Qed.

Lemma Fnd_compP A1 A2 A3 (f1 : 'F[H]_(A1,A2)) (f2 : 'F[H]_(A3,A1))
  B1 B2 B3 (g1 : 'F[H]_(B1,B2)) (g2 : 'F[H]_(B3,B1)) :
    f1 =c g1 -> f2 =c g2 -> f1 \o f2 =c g1 \o g2.
Proof.
move=>P1 P2; rewrite -[g1]to_FndK -(eq_FndP P1) -[g2]to_FndK -(eq_FndP P2).
move: (eq_Fnd1 P1) (eq_Fnd1 P2)=>/=[]Pv1 Pv2 []Pv3 Pv4; clear P1 P2 g1 g2.
by case: B1 / Pv1 Pv4; case: B2 / Pv2; case: B3 / Pv3 =>?; rewrite !castlf_id.
Qed.

Lemma Fnd_cast A1 A2 B1 B2 (eqST : (A1 = B1) * (A2 = B2)) (f : 'F[H]_(_,_)) :
  (castlf eqST f) =c f.
Proof. by move: eqST=>[] Pv1 Pv2; case: _ / Pv1; case: _ / Pv2; rewrite castlf_id. Qed.

Lemma Fnd_eq1 A B :
  A = B -> (\1 : 'F[H]_A) =c (\1 : 'F[H]_B).
Proof. by move=>P; case: B / P. Qed.

Lemma Fnd_eq0 A B A' B' :
  A = A' -> B = B' -> (0 : 'F[H]_(A,B)) =c (0 : 'F[H]_(A',B')).
Proof. by move=>P1 P2; case: A' / P1; case: B' / P2. Qed.

Lemma to_Fnd_compE A1 A2 A3 (f1 : 'F[H]_(A1,A2)) (f2 : 'F[H]_(A3,A1)) :
  to_Fnd (f1 \o f2) = Fnd_dot f1 f2.
Proof.
rewrite -to_Fnd_dotE dot_lfun.unlock; apply/Fnd_compP; rewrite -[X in to_Fnd X = _]tenf_cast1r;
by rewrite !Fnd_cast !to_Fnd_tenE; f_equal; apply/Fnd_eq1; rewrite setDv.
Qed.

Lemma to_Fnd_sdotE A1 A2 (f1 : 'F[H]_A1) (f2 : 'F[H]_A2) :
  to_Fnd (f1 \O f2) = Fnd_dot f1 f2.
Proof. by rewrite sdot_lfun.unlock Fnd_cast to_Fnd_dotE. Qed.

Definition to_FndE := (to_Fnd_adjE, to_Fnd_conjE, to_Fnd_trE, to_Fnd_scaleE, 
  to_Fnd_oppE, to_Fnd_compE, to_Fnd_sdotE, to_Fnd_dotE, to_Fnd_tenE).

Ltac to_Fnd := try (apply/to_Fnd_inj); rewrite ?(to_FndE, Fnd_cast).

Definition of_FndE := (of_Fnd_adjE, of_Fnd_conjE, of_Fnd_trE, of_Fnd_scaleE, 
  of_Fnd_oppE, of_Fnd_dotE, of_Fnd_tenE).

Lemma of_FndKE x y : x = y <-> to_Fnd (of_Fnd x) = to_Fnd (of_Fnd y).
Proof. by rewrite !of_FndK. Qed.


Lemma tenFA : associative (@Fnd_ten _ H).
Proof.
move=> [ ] ? ? x1 [ ] ? ? x2 [ ] ? ? x3.
by rewrite of_FndKE !of_FndE -tenf_castA Fnd_cast.
Qed.

Lemma tenFC : commutative (@Fnd_ten _ H).
Proof.
move=> [ ] ? ? x1 [ ] ? ? x2.
by rewrite of_FndKE !of_FndE -tenf_castC Fnd_cast.
Qed.

Lemma tenF1P A (x : Fnd) : A = set0 -> (x \⊗ (\1 : 'F[H]_A))%FND = x.
Proof.
move: x => [] ? ? x ->; 
by rewrite of_FndKE !of_FndE !to_FndK -[in RHS](tenf_cast1r x) Fnd_cast.
Qed.
Lemma ten1FP A x : A = set0 -> ((\1 : 'F[H]_A) \⊗ x)%FND = x.
Proof. by rewrite tenFC; apply/tenF1P. Qed.
Lemma tenF1 : right_id (\1 : 'F[H]_set0) (@Fnd_ten _ H).
Proof. by move=>x; apply/tenF1P. Qed.
Lemma ten1F : left_id (\1 : 'F[H]_set0) (@Fnd_ten _ H).
Proof. by move=>x; apply/ten1FP. Qed.

HB.instance Definition _ := Monoid.isComLaw.Build _ _ (@Fnd_ten _ H) tenFA tenFC ten1F.

Lemma tenf_cast1l A B (f: 'F[H]_(A,B))  : 
  castlf ((set0U A),(set0U B)) ((\1 : 'F[H]_set0) \⊗ f) = f.
Proof. by to_Fnd; rewrite tenFC tenF1. Qed.

Lemma dotF_sdot A B (f: 'F[H]_A) (g: 'F[H]_B) :
  to_Fnd (f \O g) = (f \· g)%FND.
Proof. by rewrite sdot_lfun.unlock Fnd_cast. Qed.

Lemma dotF_comp A1 A2 A3 (f: 'F[H]_(A1, A2)) (g: 'F[H]_(A3, A1)) :
  to_Fnd (f \o g) = (f \· g)%FND.
Proof.
by rewrite -to_Fnd_dotE dot_lfun.unlock; apply/Fnd_compP; rewrite ?Fnd_cast to_FndE setDv tenF1.
Qed.

Definition to_FndEV := (to_Fnd_adjE, to_Fnd_conjE, to_Fnd_trE, to_Fnd_scaleE, 
  to_Fnd_oppE, dotF_sdot, dotF_comp, to_Fnd_tenE).

Lemma tenF11 A1 A2 : ((\1 : 'F[H]_A1) \⊗ (\1 : 'F[H]_A2))%FND = (\1 : 'F[H]_(A1 :|: A2)).
Proof. by rewrite -!to_FndEV tenf11. Qed.

Lemma tenfm_bij (F G : finType) (f : G -> F) (bf : bijective f) 
  (dt cdt : F -> {set I})  (u : forall i : F, 'F[H]_(dt i, cdt i)) :
    tenfm u = castlf (tenvm_bij_cast bf dt, tenvm_bij_cast bf cdt) 
      (tenfm (fun i => u (f i))).
Proof.
apply/lfunPD=>i; rewrite castlfE/= deltav_cast !tenfmdv.
rewrite (tenvm_bij bf); f_equal; apply/tenvmP=>j; do ? f_equal.
rewrite /flatidx !ffunE; apply/idxP=>k.
rewrite !idxE castidxE incl_comp; exact: idx_incl_id2.
Qed.

Lemma tenfm_cast (F : finType) (s1 t1 s2 t2 : F -> {set I}) 
  (PC1 : forall i, s1 i = s2 i) (PC2 : forall i, t1 i = t2 i) 
    (u : forall i, 'F[H]_(s1 i, t1 i)) :
    tenfm (fun i => castlf (PC1 i, PC2 i) (u i)) = 
      castlf (eq_bigcup_cast PC1, eq_bigcup_cast PC2) (tenfm u).
Proof.
move: PC1 PC2 {+}PC1 {+}PC2 u => /funext -> /funext -> PC1 PC2 u; rewrite castlf_id.
by under [X in tenfm X]functional_extensionality_dep do rewrite castlf_id.
Qed.

Lemma to_Fnd_tens (J : finType) (s t : J -> {set I}) (v : forall j : J, 'F[H]_(s j, t j)) :
  to_Fnd (tenfm v) = (\tenf_(j : J) (to_Fnd (v j)))%FND.
Proof.
pose h := (fun i : 'I_#|J| => enum_val i).
have bf : bijective h.
  by exists enum_rank; [ exact: enum_valK | exact: enum_rankK ] .
rewrite (tenfm_bij bf) Fnd_cast.
rewrite (reindex h)/=.
  exists enum_rank=>? _; by [rewrite enum_valK | rewrite /h enum_rankK].
set su := [tuple i => s (h i)].
set tu := [tuple i => t (h i)].
have PCs i : su ~_ i = s (h i) by rewrite tnthE.
have PCt i : tu ~_ i = t (h i) by rewrite tnthE.
set u := (fun i => castlf (esym (PCs i), esym (PCt i)) (v (h i))).
have PE i : v (h i) = castlf (PCs i, PCt i) (u i) by rewrite castlf_comp castlf_id.
under [RHS]eq_bigr do rewrite PE Fnd_cast.
under [X in tenfm X]functional_extensionality_dep do rewrite PE.
rewrite tenfm_cast Fnd_cast.
move: su tu {PCs PCt} u {PE}; clear; set n := #|J|; move: n.
elim.
  move=>su tu u. rewrite [RHS]big_ord0. 
  have P0 (s : 0.-tuple {set I}) : set0 = \bigcup_i (s ~_ i) by rewrite big_ord0.
  suff ->: tenfm u = castlf (P0 su, P0 tu) \1 by rewrite Fnd_cast.
  apply/lfunPD=>i; rewrite tenfmdv; apply/cdvP=>j.
  by rewrite cdv_tm big_ord0 castlfE lfunE/= deltav_cast cdv_castV !idx0E cdv_dv eqxx.
move=>n IH su; case/tupleP: su=>s su tu; case/tupleP: tu=>t tu u.
move: (tenfm_recl u)=>/(f_equal (@to_Fnd _ _ )).
rewrite Fnd_cast=>->; rewrite to_FndE big_ord_recl; f_equal=>/=.
have PCs i : su ~_ i = [tuple of s :: su] ~_ (nlift ord0 i).
  by rewrite tnthS.
have PCt i : tu ~_ i = [tuple of t :: tu] ~_ (nlift ord0 i).
  by rewrite tnthS.
pose v i := castlf (esym (PCs i), esym (PCt i)) (u (nlift ord0 i)).
have PE i : u (nlift ord0 i) = castlf (PCs i, PCt i) (v i).
  by rewrite /v castlf_comp castlf_id.
under [RHS]eq_bigr do rewrite PE Fnd_cast.
under [X in tenfm X]functional_extensionality_dep do rewrite PE.
rewrite tenfm_cast Fnd_cast. apply: IH.
Qed.

Lemma dotFE x1 x2 : (x1 \· x2)%FND = 
  ((x1 \⊗ (\1 : 'F_(tcdom x2 :\: tdom x1))) \· (x2 \⊗ (\1 : 'F_(tdom x1 :\: tcdom x2))) )%FND.
Proof.
move: x1 x2 => []?? x1 []?? x2.
by rewrite -to_FndE dot_lfun.unlock dotF_comp Fnd_cast to_FndE.
Qed.

Lemma dotFA_cond x1 x2 x3 :
  [disjoint tdom x2 & tdom x1 :\: tcdom x2] -> [disjoint tcdom x2 & tcdom x3 :\: tdom x2] ->
  (x1 \· (x2 \· x3))%FND = (x1 \· x2 \· x3)%FND.
Proof.
move: x1 x2 x3 => []A1 B1 x1 []A2 B2 x2 []A3 B3 x3/= P1 P2.
rewrite -!to_FndE dot_lfun.unlock !tenf_comp1r/=; last first.
rewrite -comp_lfunA !(to_FndE, Fnd_cast) -?tenFA !tenF11; 
do ! f_equal; apply Fnd_eq1.
2,4,5: move: P1 P2; setdec.
all: move: P1 P2; rewrite -!setI_eq0 =>/eqP/setP P1 /eqP/setP P2.
all: apply/setP=>x; move: (P1 x) (P2 x); 
rewrite !inE; case: (x \in A1); case: (x \in A2); 
case: (x \in B2); case: (x \in B3) => //=; rewrite ?andbF//.
Qed.

(* f is square *)
Lemma dotFsA x1 x2 x3 : tdom x2 = tcdom x2 ->
  (x1 \· (x2 \· x3))%FND = (x1 \· x2 \· x3)%FND.
Proof. by move: x2=>[]/=?? h P; rewrite dotFA_cond//= P disjointXD. Qed.  

(* f is square *)
Lemma dotFA A x (f: 'F[H]_A) y : 
  (x \· (f \· y))%FND = (x \· f \· y)%FND.
Proof. by rewrite dotFsA. Qed.

Lemma dotFT x1 x2 :
  [disjoint tdom x1 & tcdom x2] -> (x1 \· x2)%FND = (x1 \⊗ x2)%FND.
Proof.
move: x1 x2=>[]?? x1 []?? x2/= P3.
rewrite -!to_FndE dot_lfun.unlock.
have ->: ten_lfun x1 x2 = (ten_lfun x1 \1) \o (ten_lfun \1 x2).
by rewrite -tenf_comp// comp_lfun1l comp_lfun1r.
rewrite !(to_FndE, Fnd_cast); f_equal; last rewrite tenFC; f_equal;
by apply Fnd_eq1; apply/setDidPl=>//; rewrite disjoint_sym.
Qed.

Lemma dotFC x1 x2 : 
  [disjoint tdom x1 & tcdom x2] -> [disjoint tcdom x1 & tdom x2] ->
  (x1 \· x2)%FND = (x2 \· x1)%FND.
Proof. by move=>P1 P2; rewrite !dotFT// 1?tenFC// disjoint_sym. Qed.

Lemma dotF1P x A : A = set0 -> (x \· (\1 : 'F[H]_A))%FND = x.
Proof. by case: x=>?? x->; rewrite dotFT ?tenF1// disjointX0. Qed.
Lemma dot1FP x A : A = set0 -> ((\1 : 'F[H]_A) \· x)%FND = x.
Proof. by case: x=>?? x->; rewrite dotFT ?ten1F// disjoint0X. Qed.
Lemma dotF1 x : (x \· (\1 : 'F[H]_set0))%FND = x.
Proof. by apply/dotF1P. Qed.
Lemma dot1F x : ((\1 : 'F[H]_set0) \· x)%FND = x.
Proof. by apply/dot1FP. Qed.

Lemma dotIFP A B x : A :\: tcdom x = B :\: tcdom x ->
  ((\1 : 'F[H]_A) \· x)%FND = ((\1 : 'F[H]_B) \· x)%FND.
Proof.
move=>P; rewrite dotFE [RHS]dotFE !tenF11; do 2 f_equal; 
by apply Fnd_eq1=>//=; rewrite setUDS P setUDS.
Qed.
Lemma dotFIP A B x : A :\: tdom x = B :\: tdom x ->
  (x \· (\1 : 'F[H]_A))%FND = (x \· (\1 : 'F[H]_B))%FND.
Proof.
move=>P; rewrite dotFE [RHS]dotFE !tenF11; do 2 f_equal; 
by apply Fnd_eq1=>//=; rewrite setUDS P setUDS.
Qed.
Lemma dotIF A x :
  ((\1 : 'F[H]_A) \· x)%FND = ((\1 : 'F[H]_(A :\: tcdom x)) \· x)%FND.
Proof. by apply/dotIFP; rewrite setDDl setUid. Qed.
Lemma dotFI A x : 
  (x \· (\1 : 'F[H]_A))%FND = (x \· (\1 : 'F[H]_(A :\: tdom x)))%FND.
Proof. by apply/dotFIP; rewrite setDDl setUid. Qed.

(* using sdot for quantum operation, measurement, etc... *)
Lemma sdotFA A1 A2 A3 (f: 'F[H]_A1) (g: 'F[H]_A2) (h: 'F[H]_A3) : 
  (f \O (g \O h)) =c ((f \O g) \O h).
Proof. by rewrite !to_FndE dotFsA. Qed.  

Lemma sdotFT A B (f: 'F[H]_A) (g: 'F[H]_B) :
  [disjoint A & B] -> to_Fnd (f \O g) = (f \⊗ g)%FND.
Proof. by move=>P; rewrite !to_FndE dotFT. Qed.  

Lemma sdotFC A B (f: 'F[H]_A) (g: 'F[H]_B) : 
  [disjoint A & B] -> (f \O g) =c (g \O f).
Proof. by move=>P; rewrite !to_FndE dotFC. Qed.  

Lemma sdotF1P A B (f: 'F[H]_A) : B = set0 ->
  f \O (\1 : 'F[H]_B) =c f.
Proof. by move=>P; rewrite to_FndE dotF1P. Qed.  
Lemma sdot1FP A B (f: 'F[H]_A) : B = set0 ->
  (\1 : 'F[H]_B) \O f =c f.
Proof. by move=>P; rewrite to_FndE dot1FP. Qed.  
Lemma sdotF1 A (f: 'F[H]_A) : f \O (\1 : 'F_set0) =c f.
Proof. by apply/sdotF1P. Qed.
Lemma sdot1F A (f: 'F[H]_A) : (\1 : 'F[H]_set0) \O f =c f.
Proof. by apply/sdot1FP. Qed.

Lemma sdotFIP A B C (f: 'F[H]_A) : B :\: A = C :\: A ->
  f \O (\1 : 'F[H]_B) =c f \O (\1 : 'F[H]_C).
Proof. by move=>P; rewrite !to_FndE; apply/dotFIP. Qed.
Lemma sdotIFP A B C (f: 'F[H]_A) : B :\: A = C :\: A ->
  (\1 : 'F[H]_B) \O f =c (\1 : 'F[H]_C) \O f.
Proof. by move=>P; rewrite !to_FndE; apply/dotIFP. Qed.
Lemma sdotFI A W (f: 'F[H]_A) :
  f \O (\1 : 'F[H]_W) =c f \O (\1 : 'F[H]_(W :\: A)).
Proof. by apply/sdotFIP; rewrite setDDl setUid. Qed. 
Lemma sdotIF A W (f: 'F[H]_A) :
  (\1 : 'F[H]_W) \O f =c (\1 : 'F[H]_(W :\: A)) \O f.
Proof. by apply/sdotIFP; rewrite setDDl setUid. Qed. 

Lemma sdotFIC A W (f: 'F[H]_A) :
  f \O (\1 : 'F[H]_W) =c (\1 : 'F[H]_W) \O f.
Proof. by rewrite sdotFI sdotFC -?sdotIF// disjointXD. Qed.

Lemma sdotIFT A W (f: 'F[H]_A) :
  to_Fnd ((\1 : 'F[H]_W) \O f) = ((\1 : 'F[H]_(W :\: A)) \⊗ f)%FND.
Proof. by rewrite sdotIF sdotFT// disjointDX. Qed. 

Lemma sdotFIT A W (f: 'F[H]_A) :
  to_Fnd (f \O (\1 : 'F[H]_W)) = (f \⊗ (\1 : 'F[H]_(W :\: A)))%FND.
Proof. by rewrite sdotFI sdotFT// disjointXD. Qed.

Lemma sdotF_comp A (f: 'F[H]_A) (g: 'F[H]_A) :
  f \O g =c f \o g.
Proof. by rewrite !to_FndE. Qed.  

End NonDepLfun.

Ltac to_Fnd := try (apply/to_Fnd_inj); rewrite ?(to_FndE, Fnd_cast, to_Fnd_tens).

(******************************************************************************)
(*                                  quantum.v                                 *)
(******************************************************************************)
Module TensorNotation.

Notation "''FN[' H ]_ S"  := ('FN('H[H]_S)) (only parsing) : type_scope.
Notation "''FN[' H ]_ ( S )"  := ('FN[H]_S) (only parsing) : type_scope.
Notation "''FN_' S"  := ('FN[_]_S) : type_scope.
Notation "''FN_' ( S )"  := ('FN[_]_S) (only parsing) : type_scope.
Notation "''FH[' H ]_ S"  := ('FH('H[H]_S)) (only parsing) : type_scope.
Notation "''FH[' H ]_ ( S )"  := ('FH[H]_S) (only parsing) : type_scope.
Notation "''FH_' S"  := ('FH[_]_S) : type_scope.
Notation "''FH_' ( S )"  := ('FH[_]_S) (only parsing) : type_scope.
Notation "''F+[' H ]_ S"  := ('F+('H[H]_S)) (only parsing) : type_scope.
Notation "''F+[' H ]_ ( S )"  := ('F+[H]_S) (only parsing) : type_scope.
Notation "''F+_' S"  := ('F+[_]_S) : type_scope.
Notation "''F+_' ( S )"  := ('F+[_]_S) (only parsing) : type_scope.
Notation "''FB1[' H ]_ ( S , T )"  := ('FB1('H[H]_S, 'H[H]_T)) (only parsing) : type_scope.
Notation "''FB1[' H ]_ S"  := ('FB1('H[H]_S)) (only parsing) : type_scope.
Notation "''FB1[' H ]_ ( S )"  := ('FB1('H[H]_S)) (only parsing) : type_scope.
Notation "''FB1_' ( S , T )"  := ('FB1[_]_(S,T)) : type_scope.
Notation "''FB1_' S"  := ('FB1[_]_S) : type_scope.
Notation "''FI_' ( S )"  := ('FB1[_]_S) (only parsing) : type_scope.
Notation "''FO[' H ]_ S"  := ('FO('H[H]_S)) (only parsing) : type_scope.
Notation "''FO[' H ]_ ( S )"  := ('FO[H]_S) (only parsing) : type_scope.
Notation "''FO_' S"  := ('FO[_]_S) : type_scope.
Notation "''FO_' ( S )"  := ('FO[_]_S) (only parsing) : type_scope.
Notation "''FD[' H ]_ S"  := ('FD('H[H]_S)) (only parsing) : type_scope.
Notation "''FD[' H ]_ ( S )"  := ('FD[H]_S) (only parsing) : type_scope.
Notation "''FD_' S"  := ('FD[_]_S) : type_scope.
Notation "''FD_' ( S )"  := ('FD[_]_S) (only parsing) : type_scope.
Notation "''FD1[' H ]_ S"  := ('FD1('H[H]_S)) (only parsing) : type_scope.
Notation "''FD1[' H ]_ ( S )"  := ('FD1[H]_S) (only parsing) : type_scope.
Notation "''FD1_' S"  := ('FD1[_]_S) : type_scope.
Notation "''FD1_' ( S )"  := ('FD1[_]_S) (only parsing) : type_scope.
Notation "''FP[' H ]_ S"  := ('FP('H[H]_S)) (only parsing) : type_scope.
Notation "''FP[' H ]_ ( S )"  := ('FP[H]_S) (only parsing) : type_scope.
Notation "''FP_' S"  := ('FP[_]_S) : type_scope.
Notation "''FP_' ( S )"  := ('FP[_]_S) (only parsing) : type_scope.
Notation "''FP1[' H ]_ S"  := ('FP1('H[H]_S)) (only parsing) : type_scope.
Notation "''FP1[' H ]_ ( S )"  := ('FP1[H]_S) (only parsing) : type_scope.
Notation "''FP1_' S"  := ('FP1[_]_S) : type_scope.
Notation "''FP1_' ( S )"  := ('FP1[_]_S) (only parsing) : type_scope.
Notation "''FI[' H ]_ ( S , T )"  := ('FI('H[H]_S, 'H[H]_T)) (only parsing) : type_scope.
Notation "''FI[' H ]_ S"  := ('FI('H[H]_S)) (only parsing) : type_scope.
Notation "''FI[' H ]_ ( S )"  := ('FI('H[H]_S)) (only parsing) : type_scope.
Notation "''FI_' ( S , T )"  := ('FI[_]_(S,T)) : type_scope.
Notation "''FI_' S"  := ('FI[_]_S) (only parsing) : type_scope.
Notation "''FI_' ( S )"  := ('FI[_]_S) (only parsing) : type_scope.
Notation "''FU[' H ]_ S"  := ('FU('H[H]_S)) (only parsing) : type_scope.
Notation "''FU[' H ]_ ( S )"  := ('FU[H]_S) (only parsing) : type_scope.
Notation "''FU_' S"  := ('FU[_]_S) : type_scope.
Notation "''FU_' ( S )"  := ('FU[_]_S) (only parsing) : type_scope.

Notation "''PONB[' H ]_ ( F ; S )" := ('PONB(F ; 'H[H]_S)) (only parsing) : type_scope.
Notation "''PONB_' ( F ; S )" := ('PONB[_]_(F;S)) : type_scope.
Notation "''ONB[' H ]_ ( F ; S )" := ('ONB(F ; 'H[H]_S)) (only parsing) : type_scope.
Notation "''ONB_' ( F ; S )" := ('ONB[_]_(F ; 'H[_]_S)) : type_scope.

Notation "''PS[' H ]_ S" := ('PS('H[H]_S))   (only parsing) : type_scope.
Notation "''PS[' H ]_ ( S )" := ('PS[H]_S)    (only parsing) : type_scope.
Notation "''PS_' S"  := ('PS[_]_S) : type_scope.
Notation "''PS_' ( S )" := ('PS_S) (only parsing) : type_scope.
Notation "''NS[' H ]_ S" := ('NS('H[H]_S))   (only parsing) : type_scope.
Notation "''NS[' H ]_ ( S )" := ('NS[H]_S)    (only parsing) : type_scope.
Notation "''NS_' S"  := ('NS[_]_S) : type_scope.
Notation "''NS_' ( S )" := ('NS_S) (only parsing) : type_scope.

Notation "''TN[' H ]_ ( F ; S , T )" := ('TN(F ; 'H[H]_S , 'H[H]_T)) 
  (only parsing): type_scope.
Notation "''TN[' H ]_ ( F ; S )" := ('TN[H]_(F;S,S)) (only parsing): type_scope.
Notation "''TN_' ( F ; S , T )" := ('TN[_]_(F;S,T)) : type_scope.
Notation "''TN_' ( F ; S )" := ('TN[_]_(F;S)) : type_scope.
Notation "''QM[' H ]_ ( F ; S , T )" := ('QM(F ; 'H[H]_S , 'H[H]_T)) 
  (only parsing): type_scope.
Notation "''QM[' H ]_ ( F ; S )" := ('QM[H]_(F;S,S)) (only parsing): type_scope.
Notation "''QM_' ( F ; S , T )" := ('QM[_]_(F;S,T)) : type_scope.
Notation "''QM_' ( F ; S )" := ('QM[_]_(F;S)) : type_scope.

Notation "''SO[' H ]_ ( S , T )" := ('SO ('H[H]_S , 'H[H]_T)) (only parsing): type_scope.
Notation "''SO[' H ]_ S" := 'SO[H]_(S, S) (only parsing) : type_scope.
Notation "''SO[' H ]_ ( S )" := 'SO[H]_S (only parsing) : type_scope.
Notation "''SO_' ( S , T )" := 'SO[_]_(S, T) : type_scope.
Notation "''SO_' S" := 'SO_(S, S) : type_scope.
Notation "''SO_' ( S )" := 'SO_S (only parsing) : type_scope.

Notation "''CP[' H ]_ ( S , T )" := ('CP('H[H]_S,'H[H]_T)) (only parsing) : type_scope.
Notation "''CP[' H ]_ S" := ('CP[H]_(S,S))   (only parsing) : type_scope.
Notation "''CP[' H ]_ ( S )" := ('CP[H]_S)    (only parsing) : type_scope.
Notation "''CP_' ( S , T )"  := ('CP[_]_(S,T)) : type_scope.
Notation "''CP_' S"  := ('CP[_]_S) : type_scope.
Notation "''CP_' ( S )" := ('CP_S) (only parsing) : type_scope.
Notation "''QO[' H ]_ ( S , T )" := ('QO('H[H]_S,'H[H]_T)) (only parsing) : type_scope.
Notation "''QO[' H ]_ S" := ('QO[H]_(S,S))   (only parsing) : type_scope.
Notation "''QO[' H ]_ ( S )" := ('QO[H]_S)    (only parsing) : type_scope.
Notation "''QO_' ( S , T )"  := ('QO[_]_(S,T)) : type_scope.
Notation "''QO_' S"  := ('QO[_]_S) : type_scope.
Notation "''QO_' ( S )" := ('QO_S) (only parsing) : type_scope.
Notation "''QC[' H ]_ ( S , T )" := ('QC('H[H]_S,'H[H]_T)) (only parsing) : type_scope.
Notation "''QC[' H ]_ S" := ('QC[H]_(S,S))   (only parsing) : type_scope.
Notation "''QC[' H ]_ ( S )" := ('QC[H]_S)    (only parsing) : type_scope.
Notation "''QC_' ( S , T )"  := ('QC[_]_(S,T)) : type_scope.
Notation "''QC_' S"  := ('QC[_]_S) : type_scope.
Notation "''QC_' ( S )" := ('QC_S) (only parsing) : type_scope.

(* TODO : move *)
Reserved Notation "''DQO_' S"     (at level 8, S at level 2, format "''DQO_' S").
Reserved Notation "''DQO_' ( S )" (at level 8).
Reserved Notation "''DQO_' ( S , T )" (at level 8, format "''DQO_' ( S ,  T )").
Reserved Notation "''DQO[' H ]_ S"    (at level 8, S at level 2).
Reserved Notation "''DQO[' H ]_ ( S )"     (at level 8).
Reserved Notation "''DQO[' H ]_ ( S , T )" (at level 8).
Reserved Notation "''QU_' S"     (at level 8, S at level 2, format "''QU_' S").
Reserved Notation "''QU_' ( S )" (at level 8).
Reserved Notation "''QU_' ( S , T )" (at level 8, format "''QU_' ( S ,  T )").
Reserved Notation "''QU[' H ]_ S"    (at level 8, S at level 2).
Reserved Notation "''QU[' H ]_ ( S )"     (at level 8).
Reserved Notation "''QU[' H ]_ ( S , T )" (at level 8).

Notation "''DQO[' H ]_ ( S , T )" := ('DQO('H[H]_S,'H[H]_T)) (only parsing) : type_scope.
Notation "''DQO[' H ]_ S" := ('DQO[H]_(S,S))   (only parsing) : type_scope.
Notation "''DQO[' H ]_ ( S )" := ('DQO[H]_S)    (only parsing) : type_scope.
Notation "''DQO_' ( S , T )"  := ('DQO[_]_(S,T)) : type_scope.
Notation "''DQO_' S"  := ('DQO[_]_S) : type_scope.
Notation "''DQO_' ( S )" := ('DQO_S) (only parsing) : type_scope.
Notation "''QU[' H ]_ ( S , T )" := ('QU('H[H]_S,'H[H]_T)) (only parsing) : type_scope.
Notation "''QU[' H ]_ S" := ('QU[H]_(S,S))   (only parsing) : type_scope.
Notation "''QU[' H ]_ ( S )" := ('QU[H]_S)    (only parsing) : type_scope.
Notation "''QU_' ( S , T )"  := ('QU[_]_(S,T)) : type_scope.
Notation "''QU_' S"  := ('QU[_]_S) : type_scope.
Notation "''QU_' ( S )" := ('QU_S) (only parsing) : type_scope.

End TensorNotation.
Export TensorNotation.

Section LownerorderTensorLfun.
Context {L: finType} (H: L -> chsType).
Implicit Type (S T : {set L}).

Lemma trlf_deltavl S T (f : 'F[H]_S) (g : 'F_T) (i j : 'Idx[H]_(S :|: T)) :
  \Tr ([>deltav i ; deltav j <] \o (f \⊗ g)) = 
  \Tr ([>deltav (idxSl i) ; deltav (idxSl j) <] \o f) *
  \Tr ([>deltav (idxSr i) ; deltav (idxSr j) <] \o g).
Proof. by rewrite !outp_compl !outp_trlf !adj_dotEl -tenf_dv -!cdvE cdvT. Qed.

Lemma trlf_introdvr S T (f1 f2: 'F[H]_(S,T)) :
  (forall i j, \Tr (f1 \o [>deltav i ; deltav j <]) = 
    \Tr (f2 \o [>deltav i ; deltav j <])) <-> (f1 = f2).
Proof.
split=>[P|->//]; apply/lfunPD=>i; apply/cdvP=>j. 
by rewrite !cdv.unlock -!outp_trlf -!outp_compr P.
Qed.

Lemma trlf_introdvl S T (f1 f2: 'F[H]_(S,T)) :
  (forall i j, \Tr ([>deltav i ; deltav j <] \o f1) = 
    \Tr ([>deltav i ; deltav j <] \o f2)) <-> (f1 = f2).
Proof.
rewrite -trlf_introdvr; split=>P i j; move: (P i j);
by rewrite ![\Tr (outp _ _ \o _)]lftraceC.
Qed.

Lemma castlf_trlf S S' (eqS : S = S') (x : 'F[H]_S) :
  \Tr x = \Tr (castlf (eqS,eqS) x).
Proof. by case: S' / eqS; rewrite castlf_id. Qed.

Lemma lef_cast S S' (eqS : S = S') (f g : 'F[H]_S) :
  castlf (eqS,eqS) f ⊑ castlf (eqS,eqS) g = (f ⊑ g).
Proof. by case: S' / eqS; rewrite !castlf_id. Qed.

Lemma lef_cast_sym S S' (eqS : S = S') (f : 'F[H]_S) (g : 'F[H]_S'):
  castlf (eqS,eqS) f ⊑ g = (f ⊑ castlf (esym eqS, esym eqS) g).
Proof. by case: S' / eqS g; rewrite !castlf_id. Qed.

Lemma lef_cast_symV S S' (eqS : S' = S) (f : 'F[H]_S) (g : 'F[H]_S'):
  f ⊑ castlf (eqS,eqS) g = (castlf (esym eqS, esym eqS) f ⊑ g).
Proof. by case: S / eqS f; rewrite !castlf_id. Qed.

Lemma ltf_cast S S' (eqS : S = S') (f g : 'F[H]_S) :
  castlf (eqS,eqS) f ⊏ castlf (eqS,eqS) g = (f ⊏ g).
Proof. by case: S' / eqS; rewrite !castlf_id. Qed.

Lemma ltf_cast_sym S S' (eqS : S = S') (f : 'F[H]_S) (g : 'F[H]_S'):
  castlf (eqS,eqS) f ⊏ g = (f ⊏ castlf (esym eqS, esym eqS) g).
Proof. by case: S' / eqS g; rewrite !castlf_id. Qed.

Lemma ltf_cast_symV S S' (eqS : S' = S) (f : 'F[H]_S) (g : 'F[H]_S'):
  f ⊏ castlf (eqS,eqS) g = (castlf (esym eqS, esym eqS) f ⊏ g).
Proof. by case: S / eqS f; rewrite !castlf_id. Qed.

Lemma castlf_le1 S S' (eqS: S = S') (f : 'F[H]_S) : 
  castlf (eqS,eqS) f ⊑ \1 = (f ⊑ \1).
Proof. by case: S' / eqS; rewrite castlf_id. Qed.

Lemma castlf_ge0 S S' (eqS: S = S') (f : 'F[H]_S) : 
  (0 : 'F[H]_S') ⊑ castlf (eqS,eqS) f = ((0 : 'F[H]_S)  ⊑ f).
Proof. by case: S' / eqS; rewrite castlf_id. Qed.

Lemma tenf_ge0 S T (f : 'F[H]_S) (g : 'F[H]_T) :
  [disjoint S & T] -> (0 :'F[H]_S) ⊑ f -> (0 :'F[H]_T) ⊑ g -> (0 :'F[H]_(S :|: T)) ⊑ f \⊗ g.
Proof.
move=>P1 /gef0_formV[f1 Pf] /gef0_formV[g1 Pg].
by rewrite Pf Pg tenf_comp// -tenf_adj form_gef0.
Qed.

Lemma tenf_eq0 S T (dis : [disjoint S & T]) (f : 'F[H]_S) (g : 'F[H]_T) :
  f \⊗ g == 0 = (f == 0) || (g == 0).
Proof.
apply/Bool.eq_iff_eq_true; split.
move=>/eqP/lfunP P1. case: eqP=>//=; move=>/eqP/lfun_neq0P[v /negPf Pv].
apply/eqP/lfunP=>x; apply/intro_dotl=>y; 
move: (P1 (tenv v x))=>/intro_dotl/(_ (tenv (f v) y))/eqP.
by rewrite tenf_apply// tenv_dot// !lfunE/= !linear0 mulf_eq0 Pv/==>/eqP.
by move=>/orP[/eqP->|/eqP->]; rewrite ?linear0l ?linear0r eqxx.
Qed.

Lemma ptenf_rge0 S T (dis : [disjoint S & T]) (x : 'F[H]_S) (y : 'F[H]_T) :
  (0 : 'F__) ⊏ x -> ((0 : 'F__) ⊑ x \⊗ y) = ((0 : 'F__) ⊑ y).
Proof.
move=>/gtf0_pdP[xge0 [v Pv]].
apply/Bool.eq_iff_eq_true; split; last by apply: tenf_ge0=>//.
move/lef_dot=>P1. apply/lef_dot=>u.
move: (P1 (tenv v u)).
by rewrite !tenf_apply// tenv_dot// !lfunE/= !linear0 pmulr_rge0.
Qed.

Lemma ptenf_lge0 S T (dis : [disjoint S & T]) (y : 'F[H]_T) (x : 'F[H]_S) :
  (0 : 'F__) ⊏ y -> ((0 : 'F__) ⊑ x \⊗ y) = ((0 : 'F__) ⊑ x).
Proof.
by move=>Q; rewrite -tenf_castC lef_cast_symV linear0 ptenf_rge0// disjoint_sym.
Qed.

HB.instance Definition _ S T dis := isBRegVOrder.Build C 'F[H]_S 'F_T 
  'F_(S :|: T) (@ten_lfun L H S S T T) (linearBl _) (linearBr _) 
    (@tenf_eq0 S T dis) (ptenf_rge0 dis) (ptenf_lge0 dis).

Lemma ptenf_rgt0 S T (dis : [disjoint S & T]) (x : 'F[H]_S) (y : 'F[H]_T) :
  (0 : 'F__) ⊏ x -> ((0 : 'F__) ⊏ x \⊗ y) = ((0 : 'F__) ⊏ y).
Proof. exact: pbregv_rgt0. Qed.

Lemma ptenf_lgt0 S T (dis : [disjoint S & T]) (y : 'F[H]_T) (x : 'F[H]_S) :
  (0 : 'F__) ⊏ y -> ((0 : 'F__) ⊏ x \⊗ y) = ((0 : 'F__) ⊏ x).
Proof. exact: pbregv_lgt0. Qed.

(* if needed, add similar things in mxcvg : vorder scale *)
Lemma lef_tenfl S T (dis : [disjoint S & T]) (f1 f2: 'F[H]_S) (g: 'F[H]_T) :
  (0 :'F[H]_T) ⊑ g -> f1 ⊑ f2 -> f1 \⊗ g ⊑ f2 \⊗ g.
Proof. move=>p1; exact: (lev_wpbreg2r _ p1). Qed.

Lemma lef_tenfr S T (dis : [disjoint S & T]) (g: 'F[H]_S) (f1 f2: 'F[H]_T) :
  (0 :'F[H]_S) ⊑ g -> f1 ⊑ f2 -> g \⊗ f1 ⊑ g \⊗ f2.
Proof. by move=>p1; apply: (lev_wpbreg2l _ p1). Qed.

End LownerorderTensorLfun.

HB.lock Definition tenso_fun {L : finType} {H : L -> chsType} [S T S' T'] 
  (E : 'SO[H]_(S,T)) (F : 'SO_(S',T')) (x : 'F_(S :|: S')) : 'F_(T :|: T') :=
  \sum_(i : 'Idx_(S :|: S')) \sum_(j : 'Idx_(S :|: S')) (
    [< deltav i ; x (deltav j) >] *: 
    ( E [> (deltav (idxSl i)) ; (deltav (idxSl j)) <] \⊗ 
      F [> (deltav (idxSr i)) ; (deltav (idxSr j)) <] )).

Lemma tenso_fun_is_linear {L : finType} {H : L -> chsType} [S T S' T']
  (E : 'SO[H]_(S,T)) (F : 'SO[H]_(S',T')) : linear (tenso_fun E F).
Proof.
move=>a u v; rewrite tenso_fun.unlock.
do 2 (rewrite scaler_sumr -big_split /=; apply eq_bigr=>? _).
by rewrite lfunE/= lfunE/= linearP/= scalerA -scalerDl.
Qed.
HB.instance Definition _ L H S T S' T' E F := GRing.isLinear.Build C 'F_(S :|: S')
  'F_(T :|: T') *:%R (tenso_fun E F) (@tenso_fun_is_linear L H S T S' T' E F).
Definition tenso {L H} [S T S' T'] E F := Superop (linfun (@tenso_fun L H S T S' T' E F)). 

Notation "f :⊗ g" := (tenso f g) : lfun_scope.

Section SOTensor.
Context {L : finType} (H : L -> chsType).
Implicit Type (S T: {set L}).

Lemma tensodf S T S' T' (E : 'SO[H]_(S,T)) (F : 'SO[H]_(S',T')) i j :
  E [> (deltav (idxSl i)) ; (deltav (idxSl j)) <] \⊗ 
  F [> (deltav (idxSr i)) ; (deltav (idxSr j)) <]
  = (E :⊗ F) [> deltav i ; deltav j <]. 
Proof.
rewrite /tenso/=/fun_of_superof/= lfunE/= tenso_fun.unlock.
rewrite (bigD1 i)//= (bigD1 j)//= !big1=>[k/negPf nk|k/negPf nk|].
2: rewrite big1// =>[l _].
all: rewrite outpE linearZ/= !onb_dot ?nk 1?eq_sym ?nk ?mul0r ?mulr0 ?scale0r//.
by rewrite !eqxx mulr1 scale1r !addr0.
Qed.

Lemma tenso_correct S T S' T' (E : 'SO[H]_(S,T)) (F : 'SO[H]_(S',T')) : 
  [disjoint S & S'] ->
  forall (u : 'F_S) (v : 'F_S'), (E u) \⊗ (F v) = (tenso E F) (u \⊗ v).
Proof.
move=>dis u v.
rewrite (onb_lfun2id deltav u).
rewrite linear_suml !linear_sum linear_suml/=. apply eq_bigr=>i _.
rewrite linear_suml !linear_sum linear_suml/=. apply eq_bigr=>j _.
rewrite (onb_lfun2id deltav v).
rewrite linear_sumr !linear_sum/=. apply eq_bigr=>m _.
rewrite linear_sumr !linear_sum/=. apply eq_bigr=>n _.
rewrite 5 !linearZ/=; f_equal; rewrite 2 !linearZl_LR linearZ/=; congr (_ *: _).
by rewrite tenf_outp !dv_tensor//= -tensodf !idxSUl//= !idxSUr//=.
Qed.

Lemma superopPD S T (A B : 'SO[H]_(S,T)) : 
  (forall (i j : 'Idx_S), A [> deltav i ; deltav j <] = 
    B [> deltav i ; deltav j <]) <-> A = B.
Proof.
split=>[P|->//]; apply/superopP=>x; rewrite (onb_lfun2id deltav x).
do 2 (rewrite !linear_sum/=; apply eq_bigr=>? _).
by rewrite !linearZ/= P.
Qed.

Lemma linear_tenso S T S' T' E : linear (@tenso L H S T S' T' E).
Proof.
move=>a v w. apply/superopPD=>i j.
by rewrite !soE -!tensodf !soE linearPr.
Qed.
HB.instance Definition _ S T S' T' E := GRing.isLinear.Build C 'SO[H]_(S',T')
  'SO_(S :|: S', T :|: T') *:%R (@tenso L H S T S' T' E) (linear_tenso E).
Lemma linear_tensor S T S' T' E : linear ((@tenso L H S T S' T')^~ E).
Proof.
move=>a v w. apply/superopPD=>i j.
by rewrite !soE -!tensodf !soE linearPl.
Qed.
HB.instance Definition _ S T S' T' := bilinear_isBilinear.Build C 'SO[H]_(S,T)
  'SO_(S',T') 'SO_(S :|: S', T :|: T') *:%R *:%R
    (@tenso L H S T S' T') (@linear_tensor S T S' T', @linear_tenso S T S' T').

Lemma tenso_comp S T S' T' W W' (f1: 'SO[H]_(S,T)) (f2: 'SO[H]_(W,S)) 
  (g1: 'SO[H]_(S',T')) (g2: 'SO[H]_(W',S')) : [disjoint S & S'] ->
  (f1 :o f2) :⊗ (g1 :o g2) = (f1 :⊗ g1) :o (f2 :⊗ g2).
Proof.
move=>dis; apply/superopPD=>i j.
by rewrite comp_soE -!tensodf !comp_soE -tenso_correct.
Qed.

Lemma tenso_compr S T S' T' W W' (f1: 'SO[H]_(S,T)) (f2: 'SO[H]_(T,W)) 
  (g1: 'SO[H]_(S',T')) (g2: 'SO[H]_(T',W')) : [disjoint T & T'] ->
  (f1 o: f2) :⊗ (g1 o: g2) = (f1 :⊗ g1) o: (f2 :⊗ g2).
Proof. by move=>dis; rewrite !comp_soErl tenso_comp. Qed.

Lemma tenso_dual S T S' T' (f: 'SO[H]_(S,T)) (g: 'SO[H]_(S',T')) :
  (f :⊗ g)^*o = f^*o :⊗ g^*o.
Proof.
apply/superopPD=>i j. apply/trlf_introdvl=>m n.
rewrite -dualso_trlfE -!tensodf [in LHS]lftraceC !trlf_deltavl -!dualso_trlfE.
by f_equal; rewrite lftraceC.
Qed.

End SOTensor.

Section SOTensorBilinear.
Context {L : finType} (H : L -> chsType).
Variables (S T S' T' : {set L}).
Implicit Type (f: 'SO[H]_(S,T)) (g: 'SO[H]_(S',T')).

Lemma tenso0 f : f :⊗ (0: 'SO[H]_(S',T')) = 0.
Proof. exact: linear0r. Qed.

Lemma ten0so g : (0: 'SO[H]_(S,T)) :⊗ g = 0.
Proof. exact: linear0l. Qed.

Lemma tenso11 : (\:1 : 'SO[H]_S) :⊗ (\:1: 'SO[H]_S') = \:1.
Proof. by apply/superopPD=>i j; rewrite -tensodf !soE tenf_outp !dv_split. Qed.

Lemma tensoDl g (f1 f2: 'SO[H]_(S,T)) : (f1 + f2) :⊗ g = (f1 :⊗ g) + (f2 :⊗ g).
Proof. exact: linearDl. Qed.

Lemma tensoDr f (g1 g2: 'SO[H]_(S',T')) : f :⊗ (g1 + g2) = (f :⊗ g1) + (f :⊗ g2).
Proof. exact: linearDr. Qed.

Lemma tensoNl g f : (- f) :⊗ g = - (f :⊗ g).
Proof. exact: linearNl. Qed.

Lemma tensoNr f g : f :⊗ (- g) = - (f :⊗ g).
Proof. exact: linearNr. Qed.

Lemma tensoZl g (c: C) f : (c *: f) :⊗ g = c *: (f :⊗ g).
Proof. exact: linearZl_LR. Qed.

Lemma tensoZr f (c: C) g : f :⊗ (c *: g) = c *: (f :⊗ g).
Proof. exact: linearZr. Qed.

Lemma tensoBl g f1 f2 : (f1 - f2) :⊗ g = f1 :⊗ g - f2 :⊗ g.
Proof. exact: linearBl. Qed.

Lemma tensoBr f g1 g2 : f :⊗ (g1 - g2) = f :⊗ g1 - f :⊗ g2.
Proof. exact: linearBr. Qed.

Lemma tensoPl g (c: C) f1 f2: (c *: f1 + f2) :⊗ g = c *: (f1 :⊗ g) + (f2 :⊗ g).
Proof. exact: linearPl. Qed.

Lemma tensoPr f (c: C) g1 g2 : f :⊗ (c *: g1 + g2) = c *: (f :⊗ g1) + (f :⊗ g2).
Proof. exact: linearPr. Qed.

Lemma tensoMnl g f n : (f *+ n) :⊗ g = (f :⊗ g) *+ n.
Proof. exact: linearMnl. Qed.

Lemma tensoMnr f g n : f :⊗ (g *+ n) = (f :⊗ g) *+ n.
Proof. exact: linearMnr. Qed.

Lemma tensoMNnl g f n : (f *- n) :⊗ g = (f :⊗ g) *- n.
Proof. exact: linearMNnl. Qed.

Lemma tensoMNnr f g n : f :⊗ (g *- n) = (f :⊗ g) *- n.
Proof. exact: linearMNnr. Qed.

Lemma tenso_suml g I r (P: pred I) (E: I -> 'SO[H]_(S, T)) :
 (\sum_(i <- r | P i) E i) :⊗ g = \sum_(i <- r | P i) (E i :⊗ g).
Proof. exact: linear_suml. Qed.

Lemma tenso_sumr f I r (P: pred I) (E: I -> 'SO[H]_(S', T')) :
 f :⊗ (\sum_(i <- r | P i) E i) = \sum_(i <- r | P i) (f :⊗ E i).
Proof. exact: linear_sumr. Qed.

Lemma tenso_comp1r W f (h: 'SO[H]_(W,S)) : [disjoint S & S'] -> 
  (f :o h) :⊗ (\:1 : 'SO[H]_S') = (f :⊗ \:1) :o (h :⊗ \:1).
Proof. by move=>dis; rewrite -tenso_comp ?comp_so1l//. Qed.

Lemma tenso_comp1l W f (h: 'SO[H]_(W,S)) : [disjoint S' & S] -> 
  (\:1 : 'SO[H]_S') :⊗ (f :o h) = (\:1 :⊗ f) :o (\:1 :⊗ h).
Proof. by move=>dis; rewrite -tenso_comp ?comp_so1l//. Qed.

Lemma tenso_compr1r W f (h: 'SO[H]_(T,W)) : [disjoint T & T'] -> 
  (f o: h) :⊗ (\:1 : 'SO[H]_T') = (f :⊗ \:1) o: (h :⊗ \:1).
Proof. by move=>dis; rewrite -tenso_compr ?comp_sor1l//. Qed.

Lemma tenso_compr1l W f (h: 'SO[H]_(T,W)) : [disjoint T' & T] -> 
  (\:1 : 'SO[H]_T') :⊗ (f o: h) = (\:1 :⊗ f) o: (\:1 :⊗ h).
Proof. by move=>dis; rewrite -tenso_compr ?comp_sor1l//. Qed.

End SOTensorBilinear.

Section CastSO.
Context {L : finType} (H : L -> chsType).
Implicit Type (S T : {set L}).

Definition castso S T S' T' (eqST : (S = S') * (T = T')) (f : 'SO[H]_(S,T)) : 
  'SO[H]_(S',T') :=
  let: erefl in _ = T' := eqST.2 return 'SO[H]_(S',T') in
    let: erefl in _ = S' := eqST.1 return 'SO[H]_(S',T) in f.

Lemma castso_id S T erefl_ST (f : 'SO[H]_(S,T)) : castso erefl_ST f = f.
Proof. by case: erefl_ST => e_S e_T; rewrite [e_S]eq_axiomK [e_T]eq_axiomK. Qed.

Lemma castsoE S T S' T' (eqST : (S = S') * (T = T')) (f : 'SO[H]_(S,T)) u :
  castso eqST f u = castlf (eqST.2,eqST.2) (f (castlf (esym eqST.1,esym eqST.1) u)).
Proof. 
by do [case: eqST; case: S' /; case: T' /] in f u *; rewrite !castlf_id castso_id.
Qed.

Lemma castso_comp S1 T1 S2 T2 S3 T3 (eq_S1 : S1 = S2) (eq_T1 : T1 = T2)
                                    (eq_S2 : S2 = S3) (eq_T2 : T2 = T3) f :
  castso (eq_S2, eq_T2) (castso (eq_S1, eq_T1) f)
    = castso (etrans eq_S1 eq_S2, etrans eq_T1 eq_T2) f.
Proof.
by case: S2 / eq_S1 eq_S2; case: S3 /; case: T2 / eq_T1 eq_T2; case: T3 /.
Qed.

Lemma castsoK S1 T1 S2 T2 (eq_S : S1 = S2) (eq_T : T1 = T2) :
 cancel (castso (eq_S, eq_T)) (castso (esym eq_S, esym eq_T)).
Proof. by case: S2 / eq_S; case: T2 / eq_T. Qed.

Lemma castsoKV S1 T1 S2 T2 (eq_S : S1 = S2) (eq_T : T1 = T2) :
 cancel (castso (esym eq_S, esym eq_T)) (castso (eq_S, eq_T)).
Proof. by case: S2 / eq_S; case: T2 / eq_T. Qed.

(* This can be use to reverse an equation that involves a cast. *)
Lemma castso_sym S1 T1 S2 T2 (eq_S : S1 = S2) (eq_T : T1 = T2) A1 A2 :
  A1 = castso (eq_S, eq_T) A2 -> A2 = castso (esym eq_S, esym eq_T) A1.
Proof. by move/(canLR (castsoK _ _)). Qed.

Lemma castso_symV S1 T1 S2 T2 (eq_S : S1 = S2) (eq_T : T1 = T2) A1 A2 :
  A2 = castso (esym eq_S, esym eq_T) A1 -> A1 = castso (eq_S, eq_T) A2.
Proof. by move/(canLR (castsoKV _ _)). Qed.

Lemma castso_is_linear S T S' T' (eqST : (S = S') * (T = T')) : 
  linear (@castso _ _ _ _ eqST).
Proof. 
move=>a f g; case: eqST => eqS eqT; case: S' / eqS; case: T' / eqT.
by rewrite !castso_id.
Qed.
HB.instance Definition _ S T S' T' eqST := GRing.isLinear.Build C 'SO[H]_(S,T)
  'SO_(S',T') *:%R (castso eqST) (@castso_is_linear S T S' T' eqST).

Lemma castso_compl S T S' T' (eqST: S = T') (f: 'SO[H]_(S,T)) 
  (g: 'SO[H]_(S',T')) :
  castso (eqST, erefl _) f :o g = f :o castso (erefl _, esym eqST) g.
Proof.
by move: f g; case: T' / eqST => f g; rewrite !castso_id.
Qed.

Lemma castso_complV S T S' T' (eqST: T' = S) (f: 'SO[H]_(S,T)) 
  (g: 'SO[H]_(S',T')) :
  f :o castso (erefl _, eqST) g = castso (esym eqST, erefl _) f :o g.
Proof.
by move: f g; case: S / eqST => f g; rewrite !castso_id.
Qed.

Lemma castso_compr S T S' T' (eqST: T = S') (f: 'SO[H]_(S,T)) 
  (g: 'SO[H]_(S',T')) :
  castso (erefl _, eqST) f o: g = f o: castso (esym eqST, erefl _) g.
Proof.
by move: f g; case: S' / eqST => f g; rewrite !castso_id.
Qed.

Lemma castso_comprV S T S' T' (eqST: S' = T) (f: 'SO[H]_(S,T)) 
  (g: 'SO[H]_(S',T')) :
  f o: castso (eqST, erefl _) g = castso (erefl _, esym eqST) f o: g.
Proof.
by move: f g; case: T / eqST => f g; rewrite !castso_id.
Qed.

Lemma compso_cast S W T S' W' T' (A : 'SO[H]_(W,T)) (B : 'SO[H]_(S,W)) 
  (eqW : W = W') (eqT: T = T') (eqS: S = S') :
    castso (eqW,eqT) A :o castso (eqS,eqW) B = castso (eqS,eqT) (A :o B).
Proof. by case: W' / eqW; case: T' /eqT; case: S' /eqS; rewrite !castso_id. Qed.

Lemma compso_castl S W T T' (A : 'SO[H]_(W,T)) (B : 'SO[H]_(S,W)) (eqT: T = T') :
    castso (erefl _, eqT) A :o B = castso (erefl,eqT) (A :o B).
Proof. by case: T' /eqT; rewrite !castso_id. Qed.

Lemma compso_castr S W T S' (A : 'SO[H]_(W,T)) (B : 'SO[H]_(S,W)) (eqS: S = S') :
    A :o castso (eqS,erefl) B = castso (eqS,erefl) (A :o B).
Proof. by case: S' /eqS; rewrite !castso_id. Qed.

Lemma castso_dual S T S' T' (eqST : (S = S') * (T = T')) (f: 'SO[H]_(S,T)) : 
  (castso eqST f)^*o = castso (eqST.2,eqST.1) f^*o.
Proof.
by do [case: eqST; case: S' /; case: T' /] in f *; rewrite !castso_id.
Qed.

Lemma castso1 S T (eqST : (S = T)) :  (castso (eqST,eqST) \:1) = \:1.
Proof. by case: T / eqST; rewrite castso_id. Qed.

Lemma castso0 S T S' T' (eqST : (S = S') * (T = T')) :  (castso eqST 0) = 0.
Proof. by rewrite linear0. Qed.

Lemma leso_cast S T S' T' (eqST : (S = S') * (T = T')) (E F : 'SO[H]_(S,T)) :
  castso eqST E ⊑ castso eqST F = (E ⊑ F).
Proof. by case: eqST => eq1 eq2; case: S' / eq1; case: T' / eq2; rewrite !castso_id. Qed.

Lemma ltso_cast S T S' T' (eqST : (S = S') * (T = T')) (E F : 'SO[H]_(S,T)) :
  castso eqST E ⊏ castso eqST F = (E ⊏ F).
Proof. by case: eqST => eq1 eq2; case: S' / eq1; case: T' / eq2; rewrite !castso_id. Qed.

Lemma leso_cast_sym S S' T T' (eqST : (S = S') * (T = T')) (E : 'SO[H]_(S,T)) (F : 'SO[H]_(S',T')) :
  castso eqST E ⊑ F = (E ⊑ castso (esym eqST.1, esym eqST.2) F).
Proof. by case: eqST => eq1 eq2; case: S' / eq1 F; case: T' / eq2=>F; rewrite !castso_id. Qed.

Lemma leso_cast_symV S S' T T' (eqST : (S' = S) * (T' = T)) (E : 'SO[H]_(S,T)) (F : 'SO[H]_(S',T')) :
  E ⊑ castso eqST F = (castso (esym eqST.1, esym eqST.2) E ⊑ F).
Proof. by case: eqST => eq1 eq2; case: S / eq1 E; case: T / eq2=>E; rewrite !castso_id. Qed.

Lemma ltso_cast_sym S S' T T' (eqST : (S = S') * (T = T')) (E : 'SO[H]_(S,T)) (F : 'SO[H]_(S',T')) :
  castso eqST E ⊏ F = (E ⊏ castso (esym eqST.1, esym eqST.2) F).
Proof. by case: eqST => eq1 eq2; case: S' / eq1 F; case: T' / eq2=>F; rewrite !castso_id. Qed.

Lemma ltso_cast_symV S S' T T' (eqST : (S' = S) * (T' = T)) (E : 'SO[H]_(S,T)) (F : 'SO[H]_(S',T')) :
  E ⊏ castso eqST F = (castso (esym eqST.1, esym eqST.2) E ⊏ F).
Proof. by case: eqST => eq1 eq2; case: S / eq1 E; case: T / eq2=>E; rewrite !castso_id. Qed.

End CastSO.

HB.lock Definition ptraceso_fun {L : finType} {H : L -> chsType} 
  T [S] (x : 'F[H]_S) : 'F[H]_(S :\: T) :=
    \sum_(k : 'Idx[H]_(S :&: T))
    \sum_(i : 'Idx[H]_(S :\: T)) \sum_(j : 'Idx[H]_(S :\: T))
    ([< deltav (idxU k i); castlf (esym (setID S T), esym (setID S T)) x (deltav (idxU k j)) >] 
     *: [>deltav i ; deltav j <]).
Lemma ptraceso_fun_is_linear L H T S : linear (@ptraceso_fun L H T S).
Proof.
move=>a x y; rewrite ptraceso_fun.unlock.
do 3 (rewrite scaler_sumr -big_split /=; apply eq_bigr=>? _).
by rewrite linearP/= lfunE/= lfunE/= linearP/= scalerDl scalerA.
Qed.
HB.instance Definition _ L H T S := GRing.isLinear.Build C 'F[H]_S
  'F_(S :\: T) *:%R (@ptraceso_fun L H T S) (@ptraceso_fun_is_linear L H T S).
Definition ptraceso {L H} T {S} := Superop (linfun (@ptraceso_fun L H T S)).

Notation "'\Tr_' ( T ) f " := (ptraceso T f) : lfun_scope.

(* partial trace is a quantum channel *)
Section PartialTrace.
Context {L : finType} (H : L -> chsType).
Implicit Type (S T W : {set L}).

Lemma ptraceso_krausso T S : @ptraceso L H T S =
  krausso (fun i : 'Idx[H]_(S :&: T) => castlf ((setID _ _), set0U _) 
    ([> deltav idx0; deltav i <] \⊗ (\1 : 'F_(S :\: T)))).
Proof.
move: (disjointID S T)=>dis; apply/superopPD=>i j.
rewrite /ptraceso{1}/fun_of_superof/= lfunE/= ptraceso_fun.unlock soE.
apply eq_bigr=>k _.
rewrite (bigD1 (idxSr (castidx (esym (setID S T)) i)))//= 
  (bigD1 (idxSr (castidx (esym (setID S T)) j)))//= !big1=>[i0/negPf ni|i0/negPf ni|].
2: rewrite big1// =>j0 _.
all: rewrite castlf_outp/= !deltav_cast outpE linearZ/= !dv_split
  !idxSUl// !idxSUr// !tenv_dot// !onb_dot.
1,2: by rewrite ?ni ?[_==i0]eq_sym ?ni ?(mulr0,mul0r) scale0r.
rewrite !eqxx !mulr1 !addr0 castlf_adj/= tenf_adj adjf1 adj_outp.
rewrite castlf_complfr [X in X \o _](castlf_complf erefl) castlf_id castlf_complfl 
  castlf_comp etrans_erefl etrans_ereflV castlf_outp !deltav_cast.
rewrite !dv_split -tenf_outp castlf_complfl castlf_id -!tenf_comp// 
  comp_lfun1l comp_lfun1r outp_comp linearZl_LR/= outp_comp !dv_dot scalerA mulrC linearZl_LR !linearZ outp_dv0/=.
by to_Fnd; rewrite ten1F.
Qed.

Lemma ptraceso_qc T S : @ptraceso L H T S \is cptp.
Proof.
apply/cptpP; split; first by rewrite ptraceso_krausso is_cpmap. 
move: (disjointID S T)=>dis; apply/tpmapP=>x.
rewrite (castlf_trlf (esym (setID S T)) x) [X in _ = \Tr X](onb_lfun2id deltav).
rewrite /ptraceso {1}/fun_of_superof/= lfunE/= ptraceso_fun.unlock.
rewrite !linear_sum/= idxSsum//.
apply eq_bigr=>i _. rewrite exchange_big/= linear_sum/=.
apply eq_bigr=>j _. rewrite idxSsum// exchange_big !linear_sum/=.
apply eq_bigr=>k _. rewrite linear_sum/= (bigD1 i)//= big1=>[m/negPf nm|].
all: rewrite !linearZ/= !outp_trlf ?addr0; do ? f_equal.
suff ->: [< deltav (idxU i j); deltav (idxU m k) >] = 0 by rewrite mulr0.
all: by rewrite !dv_split tenv_dot// !idxSUl// !idxSUr// !onb_dot ?eqxx ?mul1r//
  [i == m]eq_sym nm mul0r.
Qed.
HB.instance Definition _ T S := isQChannel.Build
  'H[H]_S 'H_(S :\: T) (ptraceso T) (@ptraceso_qc T S).

Lemma castso_krausso S T S' T' (eqST : (S = S') * (T = T')) (F : finType) 
  (f : F -> 'F[H]_(S,T)) :
  castso eqST (krausso f) = krausso (fun i=> castlf eqST (f i)).
Proof. by case: eqST=>eqS eqT; case: S' / eqS; case: T' /eqT. Qed.

Lemma ptraceso_comp T W S : 
  @ptraceso L H T _ :o @ptraceso L H W S = 
    castso (erefl _, esym (setDDl _ _ _)) (@ptraceso L H (W :|: T) S).
Proof.
rewrite !ptraceso_krausso comp_krausso castso_krausso.
suff P1 : ((S :\: W) :&: T) :|: (S :&: W) = S :&: (W :|: T).
suff P2 : [disjoint (S :\: W) :&: T & S :&: W].
pose h (i : 'Idx[H]__) := (idxSl (castidx (esym P1) i), idxSr (castidx (esym P1) i)).
pose g i := castidx P1 (idxU i.1 i.2 : 'Idx[H]__).
have hK : cancel h g by move=>x; rewrite /h /g/= idxUS// castidx_comp castidx_id.
have gK : cancel g h by move=>x; rewrite /h /g/= castidx_comp castidx_id 
  idxSUl// idxSUr// -surjective_pairing.
have bh : bijective h by exists g.
apply: (krausso_reindex bh)=>i/=.
rewrite -{3}[ i](castidxKV P1) -{3}[idx0](castidxKV (setU0 _)) -deltav_cast 
  dv_split -deltav_cast dv_split -castlf_outp -tenf_outp.
to_Fnd; rewrite !idx0E -tenFA -[RHS]dotFT/=;
last (rewrite [RHS]dotFE -tenFA tenF11; do ! f_equal; apply Fnd_eq1=>/=).
all: setdec.
Qed.

End PartialTrace.

Section SOTensorTheory.
Context {L : finType} (H : L -> chsType).
Implicit Type (S T W : {set L}).

Lemma tenso_krausso S T S' T' (dis : [disjoint S & S']) (F G : finType) 
  (f : F -> 'F[H]_(S,T)) (g : G -> 'F[H]_(S',T')) :
  krausso f :⊗ krausso g = krausso (fun i : F * G => f i.1 \⊗ g i.2).
Proof.
apply/superopPD=>i j; rewrite -tensodf !soE linear_suml/=.
under eq_bigr do rewrite linear_sum/=.
rewrite pair_big/=; apply eq_bigr=>[[m n]] _/=.
by rewrite !tenf_comp// tenf_outp tenf_adj !dv_split.
Qed.

Lemma tenso_krausso_formso S T S' T' (dis : [disjoint S & S']) (F : finType) 
  (f : F -> 'F[H]_(S,T)) (g : 'F[H]_(S',T')) :
  krausso f :⊗ formso g = krausso (fun i : F => f i \⊗ g).
Proof.
rewrite tenso_krausso//.
have bh: bijective (fun i : F => (i,ord0 : 'I_1)).
by exists (fun i=>i.1)=>x//=; case: x=>a b; rewrite ord1/=.
by apply: (krausso_reindex bh).
Qed.

Lemma tenso_formso_krausso S T S' T' (dis : [disjoint S & S']) (F : finType) 
  (g : 'F[H]_(S,T)) (f : F -> 'F[H]_(S',T')) :
  formso g :⊗ krausso f = krausso (fun i : F => g \⊗ f i).
Proof.
rewrite tenso_krausso//.
have bh: bijective (fun i : F => (ord0 : 'I_1, i)).
by exists (fun i=>i.2)=>x//=; case: x=>a b; rewrite !ord1/=.
by apply: (krausso_reindex bh).
Qed.

Lemma tenso_formso S T S' T' (dis : [disjoint S & S']) (f : 'F[H]_(S,T)) (g : 'F[H]_(S',T')) :
  formso f :⊗ formso g = formso (f \⊗ g).
Proof.
apply/superopPD=>i j.
by rewrite -tensodf !soE !tenf_comp// tenf_outp tenf_adj !dv_split.
Qed.

Definition lift_lf S T (sub : S :<=: T) (f : 'F[H]_S) : 'F[H]_T :=
  castlf (setUD_sub sub, setUD_sub sub) (f \⊗ (\1 : 'F[H]_(T :\: S))). 

Definition liftso S T (sub : S :<=: T) (E : 'SO[H]_S) : 'SO[H]_T :=
  castso (setUD_sub sub, setUD_sub sub) (E :⊗ (\:1 : 'SO[H]_(T :\: S))).

Definition lift_fun S T (sub : S :<=: T) (F : finType) (f : F -> 'F[H]_S) :=
  (fun i : F => lift_lf sub (f i)).

Lemma castso_cpE S T S' T' (eqST : (S = S') * (T = T')) (E: 'SO[H]_(S,T)) :
  castso eqST E \is cpmap = (E \is cpmap).
Proof. by case: eqST => eqS eqT; case: S' / eqS; case: T' / eqT; rewrite castso_id. Qed.
Lemma castso_cp S T S' T' (eqST : (S = S') * (T = T')) (E: 'CP[H]_(S,T)) :
  castso eqST E \is cpmap.
Proof. by rewrite castso_cpE is_cpmap. Qed.
HB.instance Definition _ S T S' T' eqST (E: 'CP[H]_(S,T)) := isCPMap.Build 
  'H_S' 'H_T' (castso eqST E) (@castso_cp S T S' T' eqST E).

Lemma castso_tnE S T S' T' (eqST : (S = S') * (T = T')) (E: 'SO[H]_(S,T)) :
  castso eqST E \is tnmap = (E \is tnmap).
Proof. by case: eqST => eqS eqT; case: S' / eqS; case: T' / eqT; rewrite castso_id. Qed.
Lemma castso_tn S T S' T' (eqST : (S = S') * (T = T')) (E: 'QO[H]_(S,T)) :
  castso eqST E \is tnmap.
Proof. by rewrite castso_tnE is_tnmap. Qed.
HB.instance Definition _ S T S' T' eqST (E: 'QO[H]_(S,T)) := CPMap_isTNMap.Build 
  'H_S' 'H_T' (castso eqST E) (@castso_tn S T S' T' eqST E).

Lemma castso_tpE S T S' T' (eqST : (S = S') * (T = T')) (E: 'SO[H]_(S,T)) :
  castso eqST E \is tpmap = (E \is tpmap).
Proof. by case: eqST => eqS eqT; case: S' / eqS; case: T' / eqT; rewrite castso_id. Qed.
Lemma castso_tp S T S' T' (eqST : (S = S') * (T = T')) (E: 'QC[H]_(S,T)) :
  castso eqST E \is tpmap.
Proof. by rewrite castso_tpE is_tpmap. Qed.
HB.instance Definition _ S T S' T' eqST (E: 'QC[H]_(S,T)) := QOperation_isTPMap.Build 
  'H_S' 'H_T' (castso eqST E) (@castso_tp S T S' T' eqST E).

Lemma castso_dualtnE S T S' T' (eqST : (S = S') * (T = T')) (E: 'SO[H]_(S,T)) :
  (castso eqST E)^*o \is tnmap = (E^*o \is tnmap).
Proof. by case: eqST => eqS eqT; case: S' / eqS; case: T' / eqT; rewrite castso_id. Qed.
Lemma castso_dualtn S T S' T' (eqST : (S = S') * (T = T')) (E: 'DQO[H]_(S,T)) :
  (castso eqST E)^*o \is tnmap.
Proof. by rewrite castso_dualtnE is_dualtn. Qed.
HB.instance Definition _ S T S' T' eqST (E: 'DQO[H]_(S,T)) := CPMap_isDTNMap.Build 
  'H_S' 'H_T' (castso eqST E) (@castso_dualtn S T S' T' eqST E).

Lemma castso_dualtpE S T S' T' (eqST : (S = S') * (T = T')) (E: 'SO[H]_(S,T)) :
  (castso eqST E)^*o \is tpmap = (E^*o \is tpmap).
Proof. by case: eqST => eqS eqT; case: S' / eqS; case: T' / eqT; rewrite castso_id. Qed.
Lemma castso_dualtp S T S' T' (eqST : (S = S') * (T = T')) (E: 'QU[H]_(S,T)) :
  (castso eqST E)^*o \is tpmap.
Proof. by rewrite castso_dualtpE is_dualtp. Qed.
HB.instance Definition _ S T S' T' eqST (E: 'QU[H]_(S,T)) := DualQO_isUnitalMap.Build 
  'H_S' 'H_T' (castso eqST E) (@castso_dualtp S T S' T' eqST E).

Lemma tenso_cp S T S' T' (dis : [disjoint S & S']) 
  (E : 'CP[H]_(S,T)) (F : 'CP[H]_(S',T')) : tenso E F \is cpmap.
Proof. by rewrite krausopE (krausopE F) tenso_krausso// is_cpmap. Qed.
Canonical tenso_cpType S T S' T' dis E F := CPMap_Build (@tenso_cp S T S' T' dis E F).
Lemma tenso_qo S T S' T' (disS : [disjoint S & S']) (disT : [disjoint T & T']) 
  (E : 'QO[H]_(S,T)) (F : 'QO[H]_(S',T')) : tenso E F \is cptn.
Proof.
rewrite [X in X :⊗ _](krausopE) [X in _ :⊗ X](krausopE) tenso_krausso//.
apply/krausso_qoP. rewrite /trace_nincr -tenf11 pair_bigV/=.
under eq_bigr do under eq_bigr do rewrite tenf_adj -(tenf_comp _ _ _ _ disT).
under eq_bigr do rewrite -linear_sumr/=.
rewrite -linear_suml/=. apply: lev_pbreg2=>//.
1,2: by rewrite sumv_ge0//==>i _; rewrite form_gef0.
all: apply: krausop_tn.
Qed.
Canonical tenso_qoType S T S' T' disS disT E F := 
  QOperation_Build (@tenso_qo S T S' T' disS disT E F).
Lemma tenso_qc S T S' T' (disS : [disjoint S & S']) (disT : [disjoint T & T']) 
  (E : 'QC[H]_(S,T)) (F : 'QC[H]_(S',T')) : tenso E F \is cptp.
Proof. 
rewrite [X in X :⊗ _](krausopE) [X in _ :⊗ X](krausopE) tenso_krausso//.
apply/krausso_qcP. rewrite /trace_presv -tenf11 pair_bigV/=.
under eq_bigr do under eq_bigr do rewrite tenf_adj -(tenf_comp _ _ _ _ disT).
under eq_bigr do rewrite -linear_sumr/= qmeasure_tpE.
by rewrite -linear_suml/= qmeasure_tpE.
Qed.
Canonical tenso_qcType S T S' T' disS disT E F := 
  QChannel_Build (@tenso_qc S T S' T' disS disT E F).
Lemma tenso_dqo S T S' T' (disS : [disjoint S & S']) (disT : [disjoint T & T']) 
  (E : 'DQO[H]_(S,T)) (F : 'DQO[H]_(S',T')) : (tenso E F)^*o \is cptn.
Proof. by rewrite tenso_dual is_cptn. Qed.
Canonical tenso_dqoType S T S' T' disS disT E F := 
  DualQO_Build (@tenso_dqo S T S' T' disS disT E F).
Lemma tenso_qu S T S' T' (disS : [disjoint S & S']) (disT : [disjoint T & T']) 
  (E : 'QU[H]_(S,T)) (F : 'QU[H]_(S',T')) : (tenso E F)^*o \is cptp.
Proof. by rewrite tenso_dual is_cptp. Qed.
Canonical tenso_quType S T S' T' disS disT E F := 
  QUnital_Build (@tenso_qu S T S' T' disS disT E F).

Lemma liftso_krausso S T (sub : S :<=: T) (F : finType) (f : F -> 'F[H]_S) :
  liftso sub (krausso f) = krausso (lift_fun sub f).
Proof.
rewrite /lift_lf /liftso -castso_krausso; f_equal.
by rewrite -formso1 tenso_krausso_formso// disjointXD.
Qed.
Lemma liftso_formso S T (sub : S :<=: T) (f : 'End('H[H]_S)) :
  liftso sub (formso f) = formso (lift_lf sub f).
Proof. by rewrite liftso_krausso. Qed.

Lemma liftso_cp S T (sub : S :<=: T) (E : 'CP[H]_S) :
  liftso sub E \is cpmap.
Proof. by rewrite is_cpmap// disjointXD. Qed.
HB.instance Definition _ S T sub E := isCPMap.Build _ _ _ (@liftso_cp S T sub E).
(* Canonical liftso_cpType S T sub E := CPMap_Build (@liftso_cp S T sub E). *)
Lemma liftso_tn S T (sub : S :<=: T) (E : 'QO[H]_S) :
  liftso sub E \is tnmap.
Proof. by rewrite is_tnmap// disjointXD. Qed.
HB.instance Definition _ S T sub (E : 'QO[H]_S) := 
  CPMap_isTNMap.Build _ _ (liftso sub E) (@liftso_tn S T sub E).
Lemma liftso_tp S T (sub : S :<=: T) (E : 'QC[H]_S) :
  liftso sub E \is tpmap.
Proof. by rewrite is_tpmap// disjointXD. Qed.
HB.instance Definition _ S T sub (E : 'QC[H]_S) := 
  QOperation_isTPMap.Build _ _ (liftso sub E) (@liftso_tp S T sub E).
Lemma liftso_dualtn S T (sub : S :<=: T) (E : 'DQO[H]_S) :
  (liftso sub E)^*o \is tnmap.
Proof. by rewrite is_dualtn// disjointXD. Qed.
HB.instance Definition _ S T sub (E : 'DQO[H]_S) := 
  CPMap_isDTNMap.Build _ _ (liftso sub E) (@liftso_dualtn S T sub E).
Lemma liftso_dualtp S T (sub : S :<=: T) (E : 'QU[H]_S) :
  (liftso sub E)^*o \is tpmap.
Proof. by rewrite is_tpmap// disjointXD. Qed.
HB.instance Definition _ S T sub (E : 'QU[H]_S) := 
  DualQO_isUnitalMap.Build _ _ (liftso sub E) (@liftso_dualtp S T sub E).

Lemma liftso_is_linear S T (sub : S :<=: T) : linear (liftso sub).
Proof. by move=>a x y; rewrite /liftso linearPl/= linearP. Qed.
HB.instance Definition _ S T sub :=
  GRing.isLinear.Build C _ _ *:%R (liftso sub) (@liftso_is_linear S T sub).

Lemma lift_lf_is_linear S T (sub : S :<=: T) : linear (lift_lf sub).
Proof. by move=>a x y; rewrite /lift_lf linearPl/= linearP. Qed.
HB.instance Definition _ S T sub :=
  GRing.isLinear.Build C _ _ *:%R (lift_lf sub) (@lift_lf_is_linear S T sub).

Lemma lift_fun_tn S T (sub : S :<=: T) (F : finType) (f : 'TN[H]_(F;S)) :
  trace_nincr (lift_fun sub f).
Proof.
move: (is_cptn (liftso sub (krausso f)))=>/=.
by rewrite liftso_krausso=>/krausso_qoP.
Qed.
HB.instance Definition _ S T (sub : S :<=: T) (F : finType) (f : 'TN[H]_(F;S)) := 
  isTraceNincr.Build 'H[H]_T 'H_T F (lift_fun sub f) (lift_fun_tn sub f).
Lemma lift_fun_tp S T (sub : S :<=: T) (F : finType) (f : 'QM[H]_(F;S)) :
  trace_presv (lift_fun sub f).
Proof.
move: (is_cptp (liftso sub (krausso f)))=>/=.
by rewrite liftso_krausso=>/krausso_qcP.
Qed.
HB.instance Definition _ S T (sub : S :<=: T) (F : finType) (f : 'QM[H]_(F;S)) := 
  TraceNincr_isQMeasure.Build 'H[H]_T 'H_T F (lift_fun sub f) (lift_fun_tp sub f).

(* Lemma lift_lfE S T (sub : S :<=: T) (f: 'F[H]_S) :
  lift_lf sub f = castlf (setUD_sub sub, setUD_sub sub) (f \⊗ (\1 : 'F[H]_(T :\: S))).
Proof. by []. Qed. *)

(* TODO : move *)
Lemma castlf_norm S T S' T' (eqst : (S = S') * (T = T')) (f : 'F[H]_(S,T)) :
  `| castlf eqst f| = `|f|.
Proof. by case: eqst=>[P1 P2]; case: _ / P1; case: _ /P2; rewrite castlf_id. Qed.

Lemma castlf_i2fnorm S T S' T' (eqst : (S = S') * (T = T')) (f : 'F[H]_(S,T)) :
  i2fnorm (castlf eqst f) = i2fnorm f.
Proof. by case: eqst=>[P1 P2]; case: _ / P1; case: _ /P2; rewrite castlf_id. Qed.

Lemma castso_norm S T S' T' (eqst : (S = S') * (T = T')) (f : 'SO[H]_(S,T)) :
  `| castso eqst f | = `|f|.
Proof. by case: eqst=>[P1 P2]; case: _ / P1; case: _ /P2; rewrite castso_id. Qed.

Lemma castlf_eq0 S T S' T' (eqst : (S = S') * (T = T')) (f : 'F[H]_(S,T)) :
  (castlf eqst f == 0) = (f == 0).
Proof. by case: eqst=>[P1 P2]; case: _ / P1; case: _ /P2; rewrite castlf_id. Qed.

Section lift_lfun.
Variable (S T : {set L}) (sub : S :<=: T).

Lemma lift_lf1 : lift_lf sub (\1 : 'F_S) = \1.
Proof. by rewrite /lift_lf tenf11 castlf1. Qed.

Lemma lift_lf_lef (P Q: 'F_S) :
  (lift_lf sub P ⊑ lift_lf sub Q) = (P ⊑ Q).
Proof.
by rewrite /lift_lf lef_cast -subv_ge0 -[RHS]subv_ge0 
  -linearBl/= ptenf_lge0// ?disjointXD// ltf01.
Qed.

Lemma lift_lf_inj : injective (lift_lf sub).
Proof. by move=>P Q /eqP; rewrite eq_le !lift_lf_lef -eq_le=>/eqP. Qed.

Lemma lift_lf_cplmt (P: 'F_S) : lift_lf sub (P^⟂) = (lift_lf sub P)^⟂.
Proof. by rewrite /lift_lf tenfBl linearB/= tenf11 castlf1. Qed.

Lemma lift_lf_ge0 (P: 'F_S) : 
  (0 : 'F_S) ⊑ P = ((0 : 'F__) ⊑ lift_lf sub P).
Proof. by rewrite -lift_lf_lef linear0. Qed.

Lemma lift_lf_le1 (P: 'F_S) : P ⊑ \1 = (lift_lf sub P ⊑ \1).
Proof. by rewrite -lift_lf_lef lift_lf1. Qed.

Lemma lift_lf_adj (P: 'F_S) : lift_lf sub (P^A) = (lift_lf sub P)^A.
Proof. by rewrite /lift_lf  castlf_adj/= tenf_adj adjf1. Qed.

Lemma lift_lf_tr (P: 'F_S) : lift_lf sub (P^T) = (lift_lf sub P)^T.
Proof. by rewrite /lift_lf  castlf_tr/= tenf_tr trf1. Qed.

Lemma lift_lf_conj (P: 'F_S) : lift_lf sub (P^C) = (lift_lf sub P)^C.
Proof. by rewrite /lift_lf castlf_conj/= tenf_conj conjf1. Qed.

Lemma lift_lf_comp (P Q: 'F_S) : 
  lift_lf sub (P \o Q) = lift_lf sub P \o lift_lf sub Q.
Proof. by rewrite /lift_lf -castlf_complf -tenf_comp ?disjointXD// comp_lfun1l. Qed.

Lemma lift_lf_normalE (P: 'F_S) : P \is normallf = (lift_lf sub P \is normallf).
Proof. by rewrite !normallfE -lift_lf_adj -!lift_lf_comp (inj_eq lift_lf_inj). Qed.

Lemma lift_lf_hermE (P: 'F_S) : P \is hermlf = (lift_lf sub P \is hermlf).
Proof. by rewrite !hermlfE -lift_lf_adj (inj_eq lift_lf_inj). Qed.

Lemma lift_lf_psdE (P: 'F_S) : P \is psdlf = (lift_lf sub P \is psdlf).
Proof. rewrite !psdlfE; exact: lift_lf_ge0. Qed.

Lemma lift_lf_obsE (P: 'F_S) : P \is obslf = (lift_lf sub P \is obslf).
Proof. by rewrite !obslfE -!lift_lf_lef linear0 lift_lf1. Qed.

Lemma lift_lf_bound1E (P : 'F_S) : P \is bound1lf = (lift_lf sub P \is bound1lf).
Proof. by rewrite bound1lf_obsE [RHS]bound1lf_obsE -lift_lf_adj -lift_lf_comp -lift_lf_obsE. Qed.

Lemma lift_lf_projE (P: 'F_S) : P \is projlf = (lift_lf sub P \is projlf).
Proof.
apply/eqb_iff; split=>/projlfP[P1 P2]; apply/projlfP;
move: P1 P2; rewrite -lift_lf_adj -lift_lf_comp.
by move=>->->. by move=>/lift_lf_inj+/lift_lf_inj.
Qed.

Lemma lift_lf_unitaryE (U: 'F_S) : U \is unitarylf = (lift_lf sub U \is unitarylf).
Proof. by rewrite !unitarylfE -lift_lf_adj -lift_lf_comp -(inj_eq lift_lf_inj) lift_lf1. Qed.

Lemma lift_lf_normal (P : 'FN_S) : lift_lf sub P \is normallf.
Proof. by rewrite -lift_lf_normalE is_normallf. Qed.
Lemma lift_lf_herm (P : 'FH_S) : lift_lf sub P \is hermlf.
Proof. by rewrite -lift_lf_hermE is_hermlf. Qed.
Lemma lift_lf_psd (P : 'F+_S) : lift_lf sub P \is psdlf.
Proof. by rewrite -lift_lf_psdE is_psdlf. Qed.
Lemma lift_lf_bound1 (P : 'FB1_S) : lift_lf sub P \is bound1lf.
Proof. by rewrite -lift_lf_bound1E is_bound1lf. Qed.
Lemma lift_lf_obs (P : 'FO_S) : lift_lf sub P \is obslf.
Proof. by rewrite -lift_lf_obsE is_obslf. Qed.
Lemma lift_lf_unitary (P : 'FU_S) : lift_lf sub P \is unitarylf.
Proof. by rewrite -lift_lf_unitaryE is_unitarylf. Qed.
Lemma lift_lf_proj (P : 'FP_S) : lift_lf sub P \is projlf.
Proof. by rewrite -lift_lf_projE is_projlf. Qed.

HB.instance Definition _ (P : 'FN_S) :=
  isNormalLf.Build _ (lift_lf sub P) (lift_lf_normal P).
HB.instance Definition _ (P : 'FH_S) :=
  Normal_isHermLf.Build _ (lift_lf sub P) (lift_lf_herm P).
HB.instance Definition _ (P : 'F+_S) :=
  Herm_isPsdLf.Build _ (lift_lf sub P) (lift_lf_psd P).
HB.instance Definition _ (P : 'FB1_S) :=
  isBound1Lf.Build _ _ (lift_lf sub P) (lift_lf_bound1 P).
HB.instance Definition _ (P : 'FO_S) :=
  ObsLf.Class (PsdLf.on (lift_lf sub P)) (Bound1Lf.on (lift_lf sub P)).
HB.instance Definition _ (P : 'FU_S) :=
  Bound1_isIsoLf.Build _ _ (lift_lf sub P) (unitarylf_iso (lift_lf_unitary P)).
HB.instance Definition _ (P : 'FU_S) :=
  Iso_isGisoLf.Build _ _ (lift_lf sub P) (unitarylf_giso (lift_lf_unitary P)).
HB.instance Definition _ (P : 'FP_S) :=
  Obs_isProjLf.Build _ (lift_lf sub P) (lift_lf_proj P).

Lemma lift_lf_norm (P: 'F_S) : `|lift_lf sub P| = `|P| * (dim 'H[H]_(T :\: S))%:R.
Proof. by rewrite /lift_lf castlf_norm tenf_norm ?disjointXD// trfnorm1. Qed.

Lemma lift_lf_i2fnorm (P: 'F_S) : i2fnorm (lift_lf sub P) = i2fnorm P.
Proof. by rewrite /lift_lf castlf_i2fnorm tenf_i2fnorm ?disjointXD// i2fnorm1 mulr1. Qed.

(* TODO: move, generalize to extnum *)
Lemma test (x y : C) : (forall e : C, e > 0 -> x - e <= y) -> x <= y.
move=>P.
have: (x - y >=< 0).
  apply: (@comparabler_trans _ 1); last by apply/ge_comparable.
  by apply/le_comparable; rewrite lerBlDl addrC -lerBlDl P.
case: comparableP=>//.
by rewrite subr_lt0=>/ltW.
set e : C := x - y => egt0.
have P1: y < x - e/2.
  by rewrite /e mulrBl {1}(splitr x) opprB addrC addrA subrK 
    -ltrBlDl {1}(splitr y) addrK ltr_pM2r ?invr_gt0// -subr_gt0.
have /P/(lt_le_trans P1): 0 < e / 2 by rewrite divr_gt0.
by rewrite ltxx.
by move=>/eqP; rewrite subr_eq0=>/eqP->.
Qed.

Lemma lift_lf_eq0 (P : 'F_S) : (lift_lf sub P == 0) = (P == 0).
Proof.
apply/eqb_iff; split; last by move=>/eqP->; rewrite linear0.
by rewrite /lift_lf castlf_eq0 bregIv_eq0// ?disjointXD// oner_neq0.
Qed.

End lift_lfun.

Lemma lift_lf2 S T W (sub1 : S :<=: T) (sub2 : T :<=: W) (f : 'F[H]_S) :
  lift_lf sub2 (lift_lf sub1 f) = lift_lf (subset_trans sub1 sub2) f.
Proof.
rewrite /lift_lf; to_Fnd; rewrite -tenFA tenF11; f_equal; 
by apply Fnd_eq1; move: sub1 sub2; setdec.
Qed.

Lemma lift_lf_tenf1r S T W (sub : S :|: T :<=: W) (f : 'F[H]_S) :
  [disjoint S & T] ->
  lift_lf sub (f \⊗ \1) = lift_lf (subset_trans (subsetUl _ _) sub) f.
Proof.
move=>dis; rewrite /lift_lf; to_Fnd; rewrite -tenFA tenF11; f_equal; apply Fnd_eq1.
rewrite -setDDl setUD_sub//; move: dis sub.
rewrite disjoint_sym=>/setDidPl {2}<-/subUsetP[] _; apply/setSD.
Qed.

Lemma lift_lf_tenf1l S T W (sub : S :|: T :<=: W) (f : 'F[H]_T) :
  [disjoint S & T] ->
  lift_lf sub (\1 \⊗ f) = lift_lf (subset_trans (subsetUr _ _) sub) f.
Proof.
move=>dis; rewrite /lift_lf; to_Fnd; rewrite tenFC tenFA tenF11 tenFC; 
f_equal; apply Fnd_eq1; rewrite setUC [_ :|: T]setUC -setDDl setUD_sub//.
by move: dis sub=>/setDidPl{2}<-/subUsetP[] + _; apply/setSD.
Qed.

Lemma lift_lfEl S T (f : 'F[H]_S) :
  [disjoint S & T] -> lift_lf (subsetUl S T) f = f \⊗ \1.
Proof.
move=>dis; rewrite /lift_lf; to_Fnd; f_equal; apply Fnd_eq1.
by rewrite setDUl setDv set0U; apply/setDidPl; rewrite disjoint_sym.
Qed.

Lemma lift_lfEr S T (f : 'F[H]_T) :
  [disjoint S & T] -> lift_lf (subsetUr S T) f = \1 \⊗ f.
Proof.
move=>dis; rewrite /lift_lf; to_Fnd; rewrite tenFC; f_equal; apply Fnd_eq1.
by rewrite setDUl setDv setU0; apply/setDidPl.
Qed.

Lemma lift_lf_UC S T (f : 'F[H]_S) (g : 'F[H]_T) :
  [disjoint S & T] ->
  lift_lf (subsetUl S T) f \o lift_lf (subsetUr S T) g = 
  lift_lf (subsetUr S T) g \o lift_lf (subsetUl S T) f.
Proof.
by move=>dis; rewrite lift_lfEl// lift_lfEr// -!tenf_comp// !comp_lfun1l !comp_lfun1r.
Qed.

Lemma lift_lf_compT S T (f : 'F[H]_S) (g : 'F[H]_T) :
  [disjoint S & T] ->
  lift_lf (subsetUl S T) f \o lift_lf (subsetUr S T) g = f \⊗ g.
Proof.
by move=>dis; rewrite lift_lfEl// lift_lfEr// -!tenf_comp// !comp_lfun1l !comp_lfun1r.
Qed.

Lemma lift_lf_compC S T W (sub1 : S :<=: W) (sub2 : T :<=: W) (f : 'F[H]_S) (g : 'F[H]_T) :
  [disjoint S & T] ->
  lift_lf sub1 f \o lift_lf sub2 g = lift_lf sub2 g \o lift_lf sub1 f.
Proof.
move=>dis. move: (subUsetPP sub1 sub2)=>P1.
rewrite (eq_irrelevance sub1 (subset_trans (subsetUl S T) P1)) 
(eq_irrelevance sub2 (subset_trans (subsetUr S T) P1)).
by rewrite -!lift_lf2 -!lift_lf_comp lift_lf_UC.
Qed.

Lemma lift_lf_sdot S T W (sub1 : S :<=: W) (sub2 : T :<=: W) (P : 'F[H]_S) (Q : 'F[H]_T) :
  lift_lf (subUsetPP sub1 sub2) (P \O Q) = lift_lf sub1 P \o lift_lf sub2 Q.
Proof.
rewrite /lift_lf sdot_lfun.unlock dot_lfun.unlock (castlf_complf erefl) 
  -[X in (_ \o _) \⊗ X]comp_lfun1l tenf_comp; last first.
to_Fnd; rewrite -!tenFA !tenF11; do ! f_equal; apply Fnd_eq1.
all: move: sub1 sub2; setdec.
Qed.

Lemma formlf_lift S T (sub : S :<=: T) (u : 'F[H]_S) (A : 'F_S) :
  lift_lf sub (formlf u A) = formlf (lift_lf sub u) (lift_lf sub A).
Proof. by rewrite formlf.unlock !lift_lf_comp lift_lf_adj. Qed.

Lemma liftsoE S T (sub : S :<=: T) (f: 'SO[H]_S) :
  liftso sub f = castso (setUD_sub sub, setUD_sub sub) (f :⊗ \:1).
Proof. by []. Qed.

Lemma liftsoEf S T (sub : S :<=: T) (E : 'SO[H]_S) (x : 'F_S) :
  liftso sub E (lift_lf sub x) = lift_lf sub (E x).
Proof.
rewrite /liftso /lift_lf castsoE/= castlf_comp castlf_id.
by rewrite -tenso_correct ?disjointXD ?soE.
Qed.

Lemma liftso_norm S T (sub : S :<=: T) (g : 'SO_S) : `|g| <= `|liftso sub g|.
Proof.
apply/test=>e egt0; rewrite -itnormE /itnorm.
move: (csup_adherent egt0 (itnorm_set_has_sup g))=>[x Px] /ltW P1.
apply: (le_trans P1).
move: Px; rewrite /itnorm_set/==>[[y [Py1 ->]]].
apply/itnorm_ger; exists (lift_lf sub y); split.
by rewrite lift_lf_eq0 -normr_eq0 Py1 oner_neq0.
by rewrite liftsoEf !lift_lf_norm Py1 mul1r.
Qed.

Lemma liftso1 S T (sub : S :<=: T) : liftso sub \:1 = \:1.
Proof. by rewrite /liftso tenso11 castso1. Qed.

Lemma leso01 (U : chsType) : (0 : 'SO) ⊑ (\:1 : 'SO(U)). Proof. by apply/cp_geso0. Qed.
Lemma qc_neq0 (U V: chsType) (E : 'QC(U,V)) : (E : 'SO) != 0.
Proof.
apply/eqP=>P; move: P=>/(f_equal (@dualso _ _))/superopP/(_ \1)/eqP.
by rewrite dualso0 qu1_eq1 soE oner_eq0.
Qed.
Lemma qc_gt0 (U V: chsType) (E : 'QC(U,V)) : (0 : 'SO) ⊏ E.
Proof. by rewrite lt_def qc_neq0 cp_geso0. Qed.
Lemma idso_neq0 (U : chsType) : (\:1 : 'SO(U)) != 0. Proof. exact: qc_neq0. Qed.
Lemma ltso01 (U : chsType) : (0 : 'SO(U)) ⊏ \:1. Proof. exact: qc_gt0. Qed.

Lemma tenso_ge0 S T (f : 'SO[H]_S) (g : 'SO[H]_T) :
  [disjoint S & T] -> (0 :'SO) ⊑ f -> (0 :'SO) ⊑ g -> (0 :'SO) ⊑ f :⊗ g.
Proof.
move=>P1 /geso0_cpP Pf /geso0_cpP Pg; apply/geso0_cpP.
move: (tenso_cp P1 (CPMap_Build Pf) (CPMap_Build Pg))=>//.
Qed.

Lemma so_neq0P (U V : chsType) (E : 'SO(U,V)) : 
  reflect (exists f, E f != 0) (E != 0).
Proof.
apply/(iffP negP); rewrite not_existsP; apply contra_not.
by move=>P; apply/eqP/superopP=>u; move: (P u)=>/negP; rewrite negbK soE=>/eqP.
by move=>/eqP-> x; rewrite soE/= eqxx.
Qed.

Lemma tenso_eq0 S T (dis : [disjoint S & T]) (f : 'SO[H]_S) (g : 'SO[H]_T) :
  f :⊗ g == 0 = (f == 0) || (g == 0).
Proof.
apply/Bool.eq_iff_eq_true; split.
move=>/eqP/superopP P1. case: eqP=>//=; move=>/eqP/so_neq0P[v /negPf Pv].
apply/eqP/superopP=>x; move: (P1 (v \⊗ x))=>/eqP.
by rewrite -tenso_correct// !soE tenf_eq0// Pv/==>/eqP.
by move=>/orP[/eqP->|/eqP->]; rewrite ?linear0l ?linear0r eqxx.
Qed.

Lemma psdlf_decomp (U : chsType) (f : 'End(U)): f \is psdlf -> 
  exists (v : 'I_(dim U) -> U), f = \sum_i [> v i ; v i <].
Proof.
rewrite qualifE=>/diag_decomp_absorb.
set v := fun k => sqrtC (eigenval (h2mx f) k) *: eigenvec (h2mx f) k.
rewrite/==>P. exists (fun k=> c2h (v k)).
apply/h2mx_inj; rewrite P linear_sum.
by apply eq_bigr=>i _; rewrite outp.unlock/= mx2hK !c2hK.
Qed.

Lemma ge0_krausE (U V : chsType) (E : 'SO(U,V)) x : (0:'SO) ⊑ E ->
  E x = \sum_i ((krausop E i) \o x \o (krausop E i)^A)%VF.
Proof. by move=>/geso0_cpP P; move: (krausE (CPMap_Build P) x). Qed.

(* tenf_cast1l *)

Lemma gtf0_trlfP (U : chsType) (x : 'End(U)) :
  reflect (0%:VF ⊑ x /\ \Tr x > 0) (0%:VF ⊏ x).
Proof.
rewrite [_ ⊏ x]lt_def; apply/(iffP andP)=>[[P1 P2]|[P1 P2]]; split=>//; last first.
move: P2; apply/contraTN=>/eqP->; by rewrite linear0 ltxx.
rewrite lt_def psdlf_trlf ?psdlfE// andbT; move: P1; apply/contraNN=>/eqP.
rewrite lftrace_baseE=>P4. move: (gef0_formV P2)=>[g Pg].
have P3 : forall i, true -> (fun i=>[< eb i; x (eb i) >]) i = 0.
by apply: psumr_eq0P=>// i _; rewrite Pg lfunE adj_dotEr/= ge0_dotp.
suff: g = 0 by rewrite Pg=>->; rewrite comp_lfun0r.
apply/(intro_onb eb)=>i/=; rewrite lfunE/=; apply/eqP.
by rewrite -dotp_eq0 -adj_dotEr -comp_lfunE -Pg; apply/eqP/P3.
Qed.

Lemma ptenso_rge0 S T (dis : [disjoint S & T]) (x : 'SO[H]_S) (y : 'SO[H]_T) :
  (0 : 'SO) ⊏ x -> ((0 : 'SO) ⊑ x :⊗ y) = ((0 : 'SO) ⊑ y).
Proof.
rewrite lt_def=>/andP[/so_neq0P[f /eqP Pf] xge0]; 
rewrite -eqb_iff; split; last by apply: tenso_ge0.
have : exists v : 'H_S, x [> v ; v <] != 0.
  rewrite not_existsP=>P.
  have P0 v : x [> v ; v <] = 0.
  by move: (P v)=>/negP; rewrite negbK=>/eqP.
  apply Pf; move: (lf_psd_decomp f)=>[M1[M2[M3[M4]]]][]/psdlf_decomp[v1 P1]
    []/psdlf_decomp[v2 P2][]/psdlf_decomp[v3 P3][]/psdlf_decomp[v4 P4]->.
  rewrite linearB/= linearD/= linearB/= !linearZ/=.
  suff ->: x M1 = 0. suff ->: x M2 = 0. suff ->: x M3 = 0. suff ->: x M4 = 0.
  by rewrite oppr0 scaler0 !addr0.
  1: rewrite P4. 2: rewrite P3. 3: rewrite P2. 4: rewrite P1.
  1,2,3,4: by rewrite linear_sum/= big1.
move=>[v Pv] xyge0.
pose K i := castlf (set0U T, set0U T) ((v2df (deltav i.2) \⊗ \1) 
  \o (krausop (x :⊗ y) i.1) \o (v2f v \⊗ \1)).
pose c := sqrtC (\Tr (x [> v ; v <])).
have P6: 0%:VF ⊏ x [> v; v <].
  rewrite lt_def Pv/=; move: xge0=>/(geso0_cpP) P5.
  by move: (@cp_ge0 _ _ (CPMap_Build P5) _ (outp_ge0 v)).
have cgt0 : c > 0 by rewrite /c sqrtC_gt0; move: P6=>/gtf0_trlfP[].
move: (lt0r_neq0 cgt0)=> cneq0.
suff ->: y = krausso (fun i=>c^-1 *: (K i)) by apply/geso0_cpP/is_cpmap.
apply/superopP=>z; rewrite -{2}(tenf_cast1l z) kraussoE.
under eq_bigr do rewrite adjfZ !linearZl linearZr/= scalerA.
rewrite -linear_sum/= geC0_conj ?invr_ge0; first by apply/ltW.
apply: (@scalerI _ _ (c^+2) _); first by apply/expf_neq0.
rewrite scalerA mulrA expr2 mulfK// mulfV// scale1r -expr2 sqrtCK.
rewrite -[LHS]tenf_cast1l tenfZr -tenfZl.
have ->: \Tr (x [> v; v <]) *: \1 = \sum_i ((v2df (deltav i))\o(x [> v; v <])\o(v2f (deltav i))).
  rewrite (onb_trlf deltav)/= scaler_suml; apply eq_bigr=>i _.
  apply/lfunP=>u; rewrite !lfunE/= [RHS]lfunE/= v2dfE lfunE/= v2fE linearZ/= linearZ/=.
  by apply/sv2s_inj; rewrite s2svK linearZ/= mulrC.
rewrite linear_suml/= linear_sum/= pair_bigV/= exchange_big/=; apply eq_bigr=>i _.
under eq_bigr do rewrite /K/= castlf_adj/= -!castlf_complf !adjf_comp !comp_lfunA.
rewrite -linear_sum/=; f_equal; rewrite -linear_suml/=.
under eq_bigr do rewrite -!comp_lfunA; rewrite -linear_sumr/=.
suff ->: (\sum_i0 (krausop (x :⊗ y) i0 \o (v2f v \⊗ \1 \o (\1 \⊗ z \o 
  ((v2f v \⊗ \1)^A \o (krausop (x :⊗ y) i0)^A))))) = (x :⊗ y) ([> v; v<] \⊗ z).
  by rewrite -tenso_correct// tenf_adj -!tenf_comp// 
  v2df_adj comp_lfun1l adjf1 comp_lfun1r.
rewrite [RHS]ge0_krausE//; apply eq_bigr=>j _; rewrite !comp_lfunA.
by f_equal; rewrite -!comp_lfunA; f_equal; rewrite tenf_adj adjf1 -!tenf_comp 
  ?disjoint0X// !comp_lfun1l v2f_adj comp_out comp_lfun1r.
Qed.

Lemma tenso_castC S T S' T' (f: 'SO[H]_(S,T)) (g: 'SO[H]_(S',T')) : 
  castso ((setUC S S'), (setUC T T')) (f :⊗ g) = (g :⊗ f).
Proof.
apply/superopPD=>i j; rewrite castsoE/= castlf_outp/= 
  !deltav_cast -!tensodf tenf_castC; do ? f_equal.
all: by rewrite idxSl_idxR idxSr_idxR idxR_castR ?subsetUl ?subsetUr// =>P;
  rewrite [X in _ = idxR X _](eq_irrelevance _ P).
Qed.

Lemma ptenso_lge0 S T (dis : [disjoint S & T]) (y : 'SO[H]_T) (x : 'SO[H]_S) :
  (0 : 'SO) ⊏ y -> ((0 : 'SO) ⊑ x :⊗ y) = ((0 : 'SO) ⊑ x).
Proof.
by move=>Q; rewrite -tenso_castC leso_cast_symV linear0 ptenso_rge0// disjoint_sym.
Qed.

HB.instance Definition _ S T dis := isBRegVOrder.Build C _ _ _ (@tenso L H S S T T)
  (linearBl _) (linearBr _) (@tenso_eq0 S T dis) (ptenso_rge0 dis) (ptenso_lge0 dis).

Lemma ptenso_rgt0 S T (dis : [disjoint S & T]) (x : 'SO[H]_S) (y : 'SO[H]_T) :
  (0 : 'SO) ⊏ x -> ((0 : 'SO) ⊏ x :⊗ y) = ((0 : 'SO) ⊏ y).
Proof. exact: pbregv_rgt0. Qed.

Lemma ptenso_lgt0 S T (dis : [disjoint S & T]) (y : 'SO[H]_T) (x : 'SO[H]_S) :
  (0 : 'SO) ⊏ y -> ((0 : 'SO) ⊏ x :⊗ y) = ((0 : 'SO) ⊏ x).
Proof. exact: pbregv_lgt0. Qed.

Lemma liftso_leso S T (sub : S :<=: T) (P Q: 'SO[H]_S) :
  P ⊑ Q = (liftso sub P ⊑ liftso sub Q).
Proof.
by rewrite /liftso leso_cast -subv_ge0 -[RHS]subv_ge0 
  -linearBl/= ptenso_lge0// ?disjointXD// ltso01.
Qed.

Lemma liftso_inj S T (sub : S :<=: T) : injective (liftso sub).
Proof. by move=>P Q /eqP; rewrite eq_le -!liftso_leso -eq_le=>/eqP. Qed.

Lemma liftso_ge0 S T (sub : S :<=: T) (P: 'SO[H]_S) : 
  (0 : 'SO) ⊑ P = ((0 : 'SO) ⊑ liftso sub P).
Proof. by rewrite (liftso_leso sub) linear0. Qed.

Lemma liftso_le1 S T (sub : S :<=: T) (P: 'SO[H]_S) : 
  P ⊑ \:1 = (liftso sub P ⊑ \:1).
Proof. by rewrite (liftso_leso sub) liftso1. Qed.

Lemma liftso_dual S T (sub : S :<=: T) (P: 'SO[H]_S) : 
  (liftso sub P)^*o = liftso sub P^*o.
Proof. by rewrite /liftso castso_dual/= tenso_dual dualso1. Qed.

Lemma liftso_comp S T (sub : S :<=: T) (P Q: 'SO[H]_S) :
  liftso sub (P :o Q) = liftso sub P :o liftso sub Q.
Proof. by rewrite /liftso compso_cast -tenso_comp ?disjointXD ?comp_so1l//. Qed.

Lemma liftso_compr S T (sub : S :<=: T) (P Q: 'SO[H]_S) :
  liftso sub (P o: Q) = liftso sub P o: liftso sub Q.
Proof. by rewrite !comp_soErl liftso_comp. Qed.

Lemma liftsoEl S T (f : 'SO[H]_S) :
  [disjoint S & T] -> liftso (subsetUl S T) f = f :⊗ \:1.
Proof.
move=>dis; rewrite /liftso; move: (setUD_sub (subsetUl S T)).
have Pv: T = (S :|: T) :\: S.
by rewrite setDUl setDv set0U; apply/esym/setDidPl; rewrite disjoint_sym.
by case: _ / Pv=> P; rewrite castso_id.
Qed.

Lemma liftsoEr S T (f : 'SO[H]_T) :
  [disjoint S & T] -> liftso (subsetUr S T) f = \:1 :⊗ f.
Proof.
move=>dis; rewrite /liftso; move: (setUD_sub (subsetUr S T)).
have Pv: S = (S :|: T) :\: T.
by rewrite setDUl setDv setU0; apply/esym/setDidPl.
by case: _ / Pv=> P; rewrite -tenso_castC castso_comp castso_id.
Qed.

Lemma liftso_UC S T (f : 'SO[H]_S) (g : 'SO[H]_T) :
  [disjoint S & T] ->
  liftso (subsetUl S T) f :o liftso (subsetUr S T) g = 
  liftso (subsetUr S T) g :o liftso (subsetUl S T) f.
Proof.
by move=>dis; rewrite liftsoEl ?liftsoEr -?tenso_comp ?comp_so1l ?comp_so1r.
Qed.

Lemma liftso_qoE S T (sub : S :<=: T) (f : 'SO[H]_S) :
  liftso sub f \is cptn = (f \is cptn).
Proof.
apply/eqb_iff; split=>P; last first.
by rewrite (QOperation_BuildE P) is_cptn.
have P2: f \is cpmap.
  by move: P=>/cptn_cpmap; rewrite -!geso0_cpE -liftso_ge0.
move: (krausopE (CPMap_Build P2)) P=>/=->.
rewrite liftso_krausso -!krausso_qoP /trace_nincr.
under eq_bigr do rewrite /lift_fun -lift_lf_adj -lift_lf_comp.
by rewrite -linear_sum/= -lift_lf_le1.
Qed.

Lemma tenso_castA S1 T1 S2 T2 S3 T3 (f: 'SO[H]_(S1,T1)) (g: 'SO[H]_(S2,T2))
  (h: 'SO[H]_(S3,T3)) : 
 castso (setUA S1 S2 S3, setUA T1 T2 T3) (f :⊗ (g :⊗ h)) = ((f :⊗ g) :⊗ h).
Proof.
apply/superopPD=>i j; rewrite castsoE/= castlf_outp/= 
  !deltav_cast -!tensodf tenf_castA; do ? f_equal;
do ? [apply f_equal2 | apply f_equal] =>//; 
rewrite ?idxSl_idxR ?idxSr_idxR ?idxR_castR -?setUA ?subsetUl ?subsetUr// => H1; 
rewrite !idxRA; by do ? [apply f_equal2 | apply eq_irrelevance].
Qed.

Lemma tenso_castl S1 T1 S2 T2 S1' T1' (A : 'SO[H]_(S1,T1)) (B : 'SO[H]_(S2,T2)) 
  (eqS : S1 = S1') (eqT : T1 = T1') :
  castso (eqS, eqT) A :⊗ B = 
    castso (f_equal (@setU _ ^~ _) eqS, f_equal (@setU _ ^~ _) eqT) (A :⊗ B).
Proof. by case: S1' / eqS; case: T1' / eqT=>/=; rewrite !castso_id. Qed.

Lemma tenso_castr S1 T1 S2 T2 S1' T1' (A : 'SO[H]_(S1,T1)) (B : 'SO[H]_(S2,T2)) 
  (eqS : S1 = S1') (eqT : T1 = T1') :
  B :⊗ castso (eqS, eqT) A = castso (f_equal (@setU _ _) eqS, f_equal (@setU _ _) eqT) (B :⊗ A).
Proof. by case: S1' / eqS; case: T1' / eqT=>/=; rewrite !castso_id. Qed.

Lemma liftso2 S T W (sub1 : S :<=: T) (sub2 : T :<=: W) (f : 'SO[H]_S) :
  liftso sub2 (liftso sub1 f) = liftso (subset_trans sub1 sub2) f.
Proof.
rewrite /liftso tenso_castl -tenso_castA tenso11.
apply/castso_symV. rewrite !castso_comp/=.
suff P1 : (T :\: S :|: W :\: T) = W :\: S.
have P2: S :|: (T :\: S :|: W :\: T) = S :|: W :\: S by rewrite P1.
rewrite (eq_irrelevance (etrans _ _) P2).
by case: (W :\: S) / P1 P2=>P2; rewrite castso_id.
move: sub1 sub2; setdec.
Qed.

Lemma liftso_compC S T W (sub1 : S :<=: W) (sub2 : T :<=: W) (f : 'SO[H]_S) (g : 'SO[H]_T) :
  [disjoint S & T] ->
  liftso sub1 f :o liftso sub2 g = liftso sub2 g :o liftso sub1 f.
Proof.
move=>dis. move: (subUsetPP sub1 sub2)=>P1.
rewrite (eq_irrelevance sub1 (subset_trans (subsetUl S T) P1)) 
(eq_irrelevance sub2 (subset_trans (subsetUr S T) P1)).
by rewrite -!liftso2 -!liftso_comp liftso_UC.
Qed.

Lemma lift_fun2 S T W (sub1 : S :<=: T) (sub2 : T :<=: W) (F : finType) (f : F -> 'F[H]_S) :
  lift_fun sub2 (lift_fun sub1 f) = lift_fun (subset_trans sub1 sub2) f.
Proof. by rewrite /lift_fun; apply/funext=>i; rewrite lift_lf2. Qed.

Lemma lift_lf_id S (sub : S :<=: S) (f : 'F[H]_S) :
  lift_lf sub f = f.
Proof. 
by apply/(@lift_lf_inj _ _ sub); rewrite lift_lf2 (eq_irrelevance (_ sub sub) sub).
Qed.

Lemma liftso_id S (sub : S :<=: S) (E : 'SO[H]_S) :
  liftso sub E = E.
Proof. 
by apply/(@liftso_inj _ _ sub); rewrite liftso2 (eq_irrelevance (_ sub sub) sub).
Qed.

Lemma lift_fun_id S (sub : S :<=: S) (F : finType) (f : F -> 'F[H]_S) :
  lift_fun sub f = f.
Proof. by rewrite /lift_fun; apply/funext=>i; rewrite lift_lf_id. Qed. 

Lemma liftso_elemso S T (sub : S :<=: T) (F : finType) (M : F -> 'F[H]_S) i :
  liftso sub (elemso M i) = elemso (lift_fun sub M) i.
Proof. exact: liftso_formso. Qed.

Lemma liftso_ifso S T (sub : S :<=: T) (F : finType) (M : F -> 'F[H]_S) 
  (br : F -> 'SO[H]_S) :
  liftso sub (ifso M br) = ifso (lift_fun sub M) (fun i => liftso sub (br i)).
Proof.
rewrite !ifso_elem linear_sum/=; apply eq_bigr=>i _.
by rewrite liftso_comp liftso_elemso.
Qed.

Import HermitianTopology.
Lemma liftso_whileso S T (sub : S :<=: T) (M : 'TN[H]_(bool;S)) b (D : 'QO[H]_S) :
  liftso sub (whileso M b D) = whileso (lift_fun sub M) b (liftso sub D).
Proof.
rewrite whileso.unlock -linear_lim. apply: whileso_is_cvg.
suff ->: (liftso sub \o whileso_iter M b D)%FUN = 
  whileso_iter (lift_fun sub M) b (liftso sub D) by [].
apply/funext=>i/=; rewrite !whileso_iter_incrE liftso_comp liftso_elemso; f_equal.
rewrite linear_sum/=; apply eq_bigr=>j _; case: j=>/= m _.
elim: m=>[|m IH]; first by rewrite /=liftso1.
by rewrite !whileso_incrE !liftso_comp liftso_elemso IH.
Qed.

End SOTensorTheory.

Section LiftFullSpace.
Context {L : finType} (H : L -> chsType).
Implicit Type (S T W: {set L}).

Local Notation sub S := (@subsetT L S).
Lemma subsetTE S : all_equal_to (sub S).
Proof. by move=>x; rewrite /= (eq_irrelevance x (sub S)). Qed.

Definition liftf_lf S f : 'F[H]_setT := lift_lf (sub S) f.
Definition liftfso S E : 'SO[H]_setT := liftso (sub S) E.
Definition liftf_fun S (F : finType) (f : F -> 'F[H]_S) := lift_fun (sub S) f.

Lemma liftf_funE S (F : finType) (f : F -> 'F_S) : 
  liftf_fun f = (fun i=> liftf_lf (f i)).
Proof. by []. Qed.

Lemma liftfso_krausso S (F : finType) (f : F -> 'F_S) :
  liftfso (krausso f) = krausso (liftf_fun f).
Proof. exact: liftso_krausso. Qed.
Lemma liftfso_formso S (f : 'End('H_S)) :
  liftfso (formso f) = formso (liftf_lf f).
Proof. exact: liftso_formso. Qed.

HB.instance Definition _ S (E : 'CP_S) := CPMap.on (liftfso E).
HB.instance Definition _ S (E : 'QO_S) := QOperation.on (liftfso E).
HB.instance Definition _ S (E : 'QC_S) := QChannel.on (liftfso E).
HB.instance Definition _ S (E : 'DQO_S) := DualQO.on (liftfso E).
HB.instance Definition _ S (E : 'QU_S) := QUnital.on (liftfso E).

HB.instance Definition _ S := GRing.Linear.copy (@liftfso S) (@liftfso S).
HB.instance Definition _ S := GRing.Linear.copy (@liftf_lf S) (@liftf_lf S).

HB.instance Definition _ S (F : finType) (f : 'TN_(F;S)) :=
  TraceNincr.on (liftf_fun f).
HB.instance Definition _ S (F : finType) (f : 'QM_(F;S)) := 
  QMeasure.on (liftf_fun f).

Lemma liftf_lfE S (f: 'F_S) :
  liftf_lf f = castlf (setUCr S, setUCr S) (f \⊗ (\1 : 'F_(~: S))).
Proof.
rewrite /liftf_lf /lift_lf; move: (setUCr S) (setTD S)=>P1 P2.
by case: (~:S) / P2 P1=>P1; rewrite (eq_irrelevance (_ (sub _)) P1).
Qed.

Lemma liftf_lf1 S : liftf_lf (\1 : 'F_S) = \1. Proof. exact: lift_lf1. Qed.
Lemma liftf_lf_inj S : injective (@liftf_lf S). Proof. exact: lift_lf_inj. Qed.

Lemma liftf_lf_lef S (P Q: 'F_S) : (liftf_lf P ⊑ liftf_lf Q) = (P ⊑ Q).
Proof. exact: lift_lf_lef. Qed.
Lemma liftf_lf_cplmt S (P: 'F_S) : liftf_lf (P^⟂) = (liftf_lf P)^⟂.
Proof. exact: lift_lf_cplmt. Qed.
Lemma liftf_lf_ge0 S (P: 'F_S) : (0 : 'F_S) ⊑ P = ((0 : 'F__) ⊑ liftf_lf P).
Proof. exact: lift_lf_ge0. Qed.
Lemma liftf_lf_le1 S (P: 'F_S) : P ⊑ \1 = (liftf_lf P ⊑ \1).
Proof. exact: lift_lf_le1. Qed.
Lemma liftf_lf_adj S (P: 'F_S) : liftf_lf (P^A) = (liftf_lf P)^A.
Proof. exact: lift_lf_adj. Qed.
Lemma liftf_lf_tr S (P: 'F_S) : liftf_lf (P^T) = (liftf_lf P)^T.
Proof. exact: lift_lf_tr. Qed.
Lemma liftf_lf_conj S (P: 'F_S) : liftf_lf (P^C) = (liftf_lf P)^C.
Proof. exact: lift_lf_conj. Qed.
Lemma liftf_lf_comp S (P Q: 'F_S) : liftf_lf (P \o Q) = liftf_lf P \o liftf_lf Q.
Proof. exact: lift_lf_comp. Qed.

Lemma liftf_lf_normalE S (P: 'F_S) : P \is normallf = (liftf_lf P \is normallf).
Proof. exact: lift_lf_normalE. Qed.
Lemma liftf_lf_hermE S (P: 'F_S) : P \is hermlf = (liftf_lf P \is hermlf).
Proof. exact: lift_lf_hermE. Qed.
Lemma liftf_lf_psdE S (P: 'F_S) : P \is psdlf = (liftf_lf P \is psdlf).
Proof. exact: lift_lf_psdE. Qed.
Lemma liftf_lf_bound1E S (P: 'F_S) : P \is bound1lf = (liftf_lf P \is bound1lf).
Proof. exact: lift_lf_bound1E. Qed.
Lemma liftf_lf_obsE S (P: 'F_S) : P \is obslf = (liftf_lf P \is obslf).
Proof. exact: lift_lf_obsE. Qed.
Lemma liftf_lf_unitaryE S (U: 'F_S) : U \is unitarylf = (liftf_lf U \is unitarylf).
Proof. exact: lift_lf_unitaryE. Qed.
Lemma liftf_lf_projE S (P: 'F_S) : P \is projlf = (liftf_lf P \is projlf).
Proof. exact: lift_lf_projE. Qed.

HB.instance Definition _ S (P: 'FN_S) := NormalLf.on (liftf_lf P).
HB.instance Definition _ S (P: 'FH_S) := HermLf.on (liftf_lf P).
HB.instance Definition _ S (P: 'F+_S) := PsdLf.on (liftf_lf P).
HB.instance Definition _ S (P: 'FB1_S) := Bound1Lf.on (liftf_lf P).
HB.instance Definition _ S (P: 'FO_S) := ObsLf.on (liftf_lf P).
HB.instance Definition _ S (P: 'FP_S) := ProjLf.on (liftf_lf P).
HB.instance Definition _ S (P: 'FU_S) := GisoLf.on (liftf_lf P).

Lemma liftf_lf_norm S (P: 'F_S) : `|liftf_lf P| = `|P| * (dim 'H[H]_(~: S))%:R.
Proof. by rewrite /liftf_lf lift_lf_norm setTD. Qed.

Lemma liftf_lf_i2fnorm S (P: 'F_S) : i2fnorm (liftf_lf P) = i2fnorm P.
Proof. exact: lift_lf_i2fnorm. Qed.

Lemma liftf_lf_eq0 S (P : 'F_S) : (liftf_lf P == 0) = (P == 0).
Proof. exact: lift_lf_eq0. Qed.

Lemma liftf_lf2 S T (sub : S :<=: T) (f : 'F_S) :
  liftf_lf (lift_lf sub f) = liftf_lf f.
Proof. by rewrite /liftf_lf lift_lf2 subsetTE. Qed.

Lemma liftf_lfid S (f : 'F_S) : liftf_lf (liftf_lf f) = liftf_lf f.
Proof. exact: liftf_lf2. Qed.

Lemma liftf_lf_tenf1r S T (f : 'F_S) :
  [disjoint S & T] -> liftf_lf (f \⊗ (\1 : 'F_T)) = liftf_lf f.
Proof. by move=>dis; rewrite /liftf_lf lift_lf_tenf1r// subsetTE. Qed.

Lemma liftf_lf_tenf1l S T (f : 'F_T) :
  [disjoint S & T] -> liftf_lf ((\1 : 'F_S) \⊗ f) = liftf_lf f.
Proof. by move=>dis; rewrite /liftf_lf lift_lf_tenf1l// subsetTE. Qed.

Lemma liftf_lf_compC S T (f : 'F_S) (g : 'F_T) :
  [disjoint S & T] -> liftf_lf f \o liftf_lf g = liftf_lf g \o liftf_lf f.
Proof. exact: lift_lf_compC. Qed.

Lemma liftf_lf_sdot S T (P: 'F_S) (Q: 'F_T) : 
  liftf_lf (P \O Q) = liftf_lf P \o liftf_lf Q.
Proof. by rewrite -lift_lf_sdot subsetTE. Qed.

Lemma liftf_lf2_tensl S T W (sub : S :<=: T) (P : 'F_S) (R : 'F_W):
  [disjoint T & W] ->
  liftf_lf (lift_lf sub P \⊗ R) = liftf_lf (P \⊗ R).
Proof.
move=>dis; rewrite /liftf_lf /lift_lf; to_Fnd; rewrite -!tenFA; f_equal.
rewrite tenFC -tenFA tenF11; f_equal; apply/Fnd_eq1/setP=>x.
move: sub dis=>/setIidPr/setP/(_ x)+/setDidPl/setP/(_ x).
by rewrite !inE; case: (x \in S); case: (x \in T); case: (x \in W).
Qed.

Lemma liftf_lf2_tensr S T W (sub : S :<=: T) (P : 'F_S) (R : 'F_W):
  [disjoint T & W] ->
  liftf_lf (R \⊗ lift_lf sub P) = liftf_lf (R \⊗ P).
Proof.
move=>dis; rewrite /liftf_lf /lift_lf; to_Fnd; rewrite -!tenFA tenF11.
do ! f_equal; apply/Fnd_eq1/setP=>x.
move: sub dis=>/setIidPr/setP/(_ x)+/setDidPl/setP/(_ x).
by rewrite !inE; case: (x \in S); case: (x \in T); case: (x \in W).
Qed.

Lemma liftfsoE S (f: 'SO_S) : liftfso f = castso (setUCr S, setUCr S) (f :⊗ \:1).
Proof.
rewrite /liftfso /liftso; move: (setUCr S) (setTD S)=>P1 P2.
by case: (~: S) / P2 P1=>P1; rewrite (eq_irrelevance (_ (sub _)) P1).
Qed.

Lemma liftfso_norm S (g : 'SO_S) : `|g| <= `|liftfso g|.
Proof. exact: liftso_norm. Qed.

Lemma liftfsoEf S (E : 'SO_S) (x : 'F_S) : liftfso E (liftf_lf x) = liftf_lf (E x).
Proof. exact: liftsoEf. Qed.
Lemma liftfso1 S : liftfso (\:1 : 'SO_S) = \:1. Proof. exact: liftso1. Qed.
Lemma liftfso_leso S (P Q: 'SO_S) : P ⊑ Q = (liftfso P ⊑ liftfso Q).
Proof. exact: liftso_leso. Qed.
Lemma liftfso_inj S : injective (@liftfso S). Proof. exact: liftso_inj. Qed.
Lemma liftfso_ge0 S (P: 'SO_S) : (0 : 'SO) ⊑ P = ((0 : 'SO) ⊑ liftfso P).
Proof. exact: liftso_ge0. Qed.
Lemma liftfso_le1 S (P: 'SO_S) : P ⊑ \:1 = (liftfso P ⊑ \:1).
Proof. exact: liftso_le1. Qed.
Lemma liftfso_dual S (P: 'SO_S) : (liftfso P)^*o = liftfso P^*o.
Proof. exact: liftso_dual. Qed.
Lemma liftfso_comp S (P Q: 'SO_S) :liftfso (P :o Q) = liftfso P :o liftfso Q.
Proof. exact: liftso_comp. Qed.
Lemma liftfso_compr S (P Q: 'SO_S) : liftfso (P o: Q) = liftfso P o: liftfso Q.
Proof. exact: liftso_compr. Qed.

(* TODO : move quantum.v *)
Lemma liftfso_qoE S (f : 'SO[H]_S) :
  liftfso f \is cptn = (f \is cptn).
Proof. exact: liftso_qoE. Qed.

Lemma liftfso2 S T (sub : S :<=: T) (f : 'SO_S) :
  liftfso (liftso sub f) = liftfso f.
Proof. by rewrite /liftfso liftso2 subsetTE. Qed.
Lemma liftfsoid S (f : 'SO_S) : liftfso (liftfso f) = liftfso f.
Proof. exact: liftfso2. Qed.

Lemma liftfso_compC S T (f : 'SO_S) (g : 'SO_T) :
  [disjoint S & T] -> liftfso f :o liftfso g = liftfso g :o liftfso f.
Proof. exact: liftso_compC. Qed.

Lemma liftf_fun2 S T (sub : S :<=: T) (F : finType) (f : F -> 'F_S) :
  liftf_fun (lift_fun sub f) = liftf_fun f.
Proof. by rewrite /liftf_fun lift_fun2 subsetTE. Qed.

Lemma liftf_lf_id (f : 'F_setT) : liftf_lf f = f. Proof. exact: lift_lf_id. Qed.
Lemma liftfso_id (E : 'SO_setT) : liftfso E = E. Proof. exact: liftso_id. Qed.
Lemma liftf_fun_id (F : finType) (f : F -> 'F_setT) : liftf_fun f = f.
Proof. exact: lift_fun_id. Qed.

Lemma liftfso_elemso S (F : finType) (M : F -> 'F_S) i :
  liftfso (elemso M i) = elemso (liftf_fun M) i.
Proof. exact: liftso_elemso. Qed.
Lemma liftfso_ifso S (F : finType) (M : F -> 'F_S) (br : F -> 'SO_S) :
  liftfso (ifso M br) = ifso (liftf_fun M) (fun i => liftfso (br i)).
Proof. exact: liftso_ifso. Qed.
Lemma liftfso_whileso S (M : 'TN_(bool;S)) b (D : 'QO_S) :
  liftfso (whileso M b D) = whileso (liftf_fun M) b (liftfso D).
Proof. exact: liftso_whileso. Qed.

Lemma liftf_lf_cast S T (eqST : S = T) (f : 'F_S) :
  liftf_lf (castlf (eqST,eqST) f) = liftf_lf f.
Proof. by case: T / eqST; rewrite castlf_id. Qed.

Lemma liftfso_cast S T (eqST : S = T) (f: 'SO_S) : 
  liftfso (castso (eqST,eqST) f) = liftfso f.
Proof. by case: T / eqST; rewrite castso_id. Qed.

Lemma liftf_lf_compT S T (f : 'F_S) (g : 'F_T) :
  [disjoint S & T] ->
  liftf_lf f \o liftf_lf g = liftf_lf (f \⊗ g).
Proof.
move=>dis; rewrite -(liftf_lf_tenf1r _ dis) -(liftf_lf_tenf1l _ dis).
by rewrite -liftf_lf_comp -tenf_comp ?comp_lfun1l ?comp_lfun1r.
Qed.

Lemma formlf_liftf S (u : 'F[H]_S) (A : 'F_S) :
  liftf_lf (formlf u A) = formlf (liftf_lf u) (liftf_lf A).
Proof. exact: formlf_lift. Qed.

Lemma liftfsoEf_compl S T (f : 'F_S) (E : 'SO_T) g :
  [disjoint S & T] ->
  liftfso E (liftf_lf f \o g) = liftf_lf f \o liftfso E g.
Proof.
move=>dis; have ls : S :<=: ~: T by rewrite -disjointX_subset.
rewrite -(liftfso2 (subsetT _)) [liftso _ E]liftfsoE liftfso_cast -{1}(liftf_lf2 ls).
set g' := (castlf (esym(setUCr T),esym(setUCr T)) g).
have Hg: g = liftf_lf g' by rewrite liftf_lf_cast liftf_lf_id.
rewrite Hg [g'](onb_lfun2id deltav) pair_big/= !linear_sum/= 
  !linear_sumr/= linear_sum/=; apply eq_bigr=>i _.
rewrite !linearZ/= -!comp_lfunZr linearZ/=; f_equal.
move: (disjointXC T)=>lt.
rewrite !dv_split -!tenf_outp -!liftf_lf_compT// [in LHS]liftf_lf_compC//
  comp_lfunA -liftf_lf_comp [in LHS]liftf_lf_compC ?disjointCX//
   !liftf_lf_compT// !liftfsoEf -!tenso_correct// !soE -!liftf_lf_compT// 
   liftf_lf_comp !comp_lfunA; f_equal.
by rewrite liftf_lf2 liftf_lf_compC// disjoint_sym.
Qed.

Lemma liftfsoEf_compr S T (f : 'F_S) (E : 'SO_T) g :
  [disjoint S & T] ->
  liftfso E (g \o liftf_lf f) = liftfso E g \o liftf_lf f.
Proof.
move=>dis; have ls : S :<=: ~: T by rewrite -disjointX_subset.
rewrite -(liftfso2 (subsetT _)) [liftso _ E]liftfsoE liftfso_cast -{1}(liftf_lf2 ls).
set g' := (castlf (esym(setUCr T),esym(setUCr T)) g).
have Hg: g = liftf_lf g' by rewrite liftf_lf_cast liftf_lf_id.
rewrite Hg [g'](onb_lfun2id deltav) pair_big/= !linear_sum/= 
  !linear_suml/= linear_sum/=; apply eq_bigr=>i _.
rewrite !linearZ/= -!comp_lfunZl linearZ/=; f_equal.
move: (disjointXC T)=>lt.
by rewrite !dv_split -!tenf_outp -!liftf_lf_compT// -comp_lfunA -liftf_lf_comp
   !liftf_lf_compT// !liftfsoEf -!tenso_correct// !soE -!liftf_lf_compT// 
   liftf_lf_comp comp_lfunA liftf_lf2.
Qed.

End LiftFullSpace.