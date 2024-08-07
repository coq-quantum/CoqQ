(*  TODO 
  - add support to F_True and F_False
  - cut rules
  - optimize autorewrite
  - subst in setform (to speed up the decision procedure)
  - optimize br_ext_single 
*)

(*  Proof by reflection implementation of
    Anisimov, Alexander. Proof Automation for Typed Finite Sets. 2015. *)
(* -------------------------------------------------------------------- *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From elpi     Require Export elpi.
(* ------- *) Require Import BinPos Number Decimal.

(* -------------------------------------------------------------------- *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

(* -------------------------------------------------------------------- *)

(*
  The tactic setdec solves goals of the form F :

  F ::=
  | P
  | ~ F
  | F /\ F'
  | F \/ F'
  | F -> F'
  | F <-> F'

  P ::=
  | X = X'
  | S = S'
  | X \in S
  | S \subset S'

  S ::=
  | V
  | set0
  | setT
  | set1 X
  | setC S
  | setU F F'
  | setI F F'
  | setD F F'

  X ::= x1 | ... | xm (element variables)
  V ::= v1 | ... | vn (set variables)


  The tactic setdec_bool solves goals of the form Fb :

  Fb ::=
  | Pb
  | ~~ Fb
  | Fb && Fb'
  | Fb || Fb'
  | Fb ==> Fb'

  Pb ::=
  | X == X'
  | S == S'
  | X \in S
  | S \subset S'
*)

Notation eltvar := positive.

Inductive setsyn : Type :=
| FSS_empty
| FSS_full
| FSS_single of eltvar
| FSS_var   of positive
| FSS_union of setsyn & setsyn
| FSS_diff  of setsyn & setsyn
| FSS_inter of setsyn & setsyn
.

Variant setelt : Type :=
  | FE_var of eltvar
  | FE_exvar of setsyn & setsyn.

Variant setpred : Type :=
  | FSP_In    of setelt & setsyn
  | FSP_Eqelt of setelt & setelt
  | FSP_Eqset of setsyn & setsyn
  | FSP_Sub   of setsyn & setsyn.

Inductive setform : Type :=
| F_Pred  of setpred
| F_Not   of setform
| F_And   of setform & setform
| F_Or    of setform & setform
| F_Imply of setform & setform
| F_False
| F_True
.

(* eqType of syntax terms *)

Fixpoint eqp (x y : positive) :=
  match x, y with
  | xH, xH => true
  | xO a, xO b => eqp a b
  | xI a, xI b => eqp a b
  | _, _ => false
  end.

Lemma eqpP : Equality.axiom eqp.
Proof.
  move=> x y; apply: (iffP idP).
  elim: x y.
  - by move=> p Hp [] //= => p0 /Hp ->.
  - by move=> p Hp [] //= => p0 /Hp ->.
  - by case.
  - by move=> ->; elim: y => //=.
Qed.

HB.instance Definition _ := hasDecEq.Build positive eqpP.
(* Canonical positive_eqMixin := EqMixin eqpP. *)
(* Canonical positive_eqType := Eval hnf in EqType positive positive_eqMixin. *)

Fixpoint eq_setsyn x y :=
  match x, y with
  | FSS_empty, FSS_empty => true
  | FSS_full, FSS_full => true
  | FSS_single a, FSS_single b => a == b
  | FSS_var a, FSS_var b => a == b
  | FSS_union a b, FSS_union a' b' => eq_setsyn a a' && eq_setsyn b b'
  | FSS_diff a b, FSS_diff a' b' => eq_setsyn a a' && eq_setsyn b b'
  | FSS_inter a b, FSS_inter a' b' => eq_setsyn a a' && eq_setsyn b b'
  | _, _ => false
  end.

Lemma eq_eq_setsyn a :
  forall b, (a = b -> eq_setsyn a b).
Proof.
  elim: a.
  - by move=> b <-.
  - by move=> b <-.
  - move=> v b <- /=; exact: eqxx.
  - move=> v b <- /=; exact: eqxx.
    all: move=> x Hx y Hy b <- /=; by rewrite Hx // Hy.
Qed.

Lemma eq_setsyn_eq a :
  forall b, (eq_setsyn a b -> a = b).
Proof.
  elim: a.
  - by case.
  - by case.
  - by move=> x [] //= y /eqP ->.
  - by move=> x [] //= y /eqP ->.
    all: by move=> x Hx y Hy [] //= x' y' /andP [] /Hx -> /Hy ->.
Qed.

Lemma eq_setsynP : Equality.axiom eq_setsyn.
Proof.
  move=> a b; apply: (iffP idP); [apply: eq_setsyn_eq | apply: eq_eq_setsyn].
Qed.

HB.instance Definition _ := hasDecEq.Build setsyn eq_setsynP.
(* Canonical setsyn_eqMixin := EqMixin eq_setsynP. *)
(* Canonical setsyn_eqType := Eval hnf in EqType setsyn setsyn_eqMixin. *)

Definition eq_setelt x y :=
  match x, y with
  | FE_var a, FE_var b => a == b
  | FE_exvar a b, FE_exvar a' b' => (a == a') && (b == b')
  | _, _ => false
  end.

Lemma eq_seteltP : Equality.axiom eq_setelt.
Proof.
  move=> a b; apply: (iffP idP).
  - move: a => []; move: b => [] //= x y. by move/eqP=> ->.
  - by move=> a b /andP [] /eqP -> /eqP ->.
  - move=> ->; case: b => //= x y; by rewrite !eqxx.
Qed.

HB.instance Definition _ := hasDecEq.Build setelt eq_seteltP.
(* Canonical setelt_eqMixin := EqMixin eq_seteltP.
Canonical setelt_eqType := Eval hnf in EqType setelt setelt_eqMixin. *)

Definition eq_setpred a b :=
  match a, b with
  | FSP_In x y, FSP_In x' y' => (x == x') && (y == y')
  | FSP_Eqelt x y, FSP_Eqelt x' y' => (x == x') && (y == y')
  | FSP_Eqset x y, FSP_Eqset x' y' => (x == x') && (y == y')
  | FSP_Sub x y, FSP_Sub x' y' => (x == x') && (y == y')
  | _, _ => false
  end.

Lemma eq_setpredP : Equality.axiom eq_setpred.
Proof.
  move=> a b; apply: (iffP idP).
  - case: a; by case: b => //= x x' y y' => /andP [] /eqP -> /eqP ->.
  - move=> -> //=; case: b => //=; move=> x y; by rewrite !eqxx.
Qed.

HB.instance Definition _ := hasDecEq.Build setpred eq_setpredP.
(* Canonical setpred_eqMixin := EqMixin eq_setpredP.
Canonical setpred_eqType := Eval hnf in EqType setpred setpred_eqMixin. *)

Fixpoint eq_setform a b :=
  match a, b with
  | F_Pred x, F_Pred y => x == y
  | F_Not x, F_Not y => eq_setform x y
  | F_And a b, F_And a' b'  => eq_setform a a' && eq_setform b b'
  | F_Or a b, F_Or a' b'  => eq_setform a a' && eq_setform b b'
  | F_Imply a b, F_Imply a' b'  => eq_setform a a' && eq_setform b b'
  | F_False, F_False => true
  | F_True, F_True => true
  | _, _ => false
  end.

Lemma eq_setformP : Equality.axiom eq_setform.
Proof.
  move=> a b; apply (iffP idP).
  - elim: a b; try by move=> x Hx y Hy [] //= x' y' /andP [] /Hx -> /Hy ->.
    + by move=> x [] //= y /eqP ->.
    + by move=> x Hx [] //= y /Hx ->.
    + by case.
    + by case.
  - move=> ->; elim: b => //=; by move=> x -> y ->.
Qed.

HB.instance Definition _ := hasDecEq.Build setform eq_setformP.
(* Canonical setform_eqMixin := EqMixin eq_setformP.
Canonical setform_eqType := Eval hnf in EqType setform setform_eqMixin. *)

Section setform_interp.
  Context {T : finType}.

  (*  
    setvar_lst collects set variables,
    var_lst collects T variables.
  *)
  Variable (setvar_lst : seq {set T}).
  Variable (var_lst : seq T).

  (* assignment of existential variables introduced by (S3) *)
  Variable asn : setsyn -> setsyn -> option T.

  Definition sem_eltvar (x : eltvar) :=
    List.nth_error var_lst (nat_of_pos x - 1).

  Definition sem_singleton (x : eltvar) :=
    match (sem_eltvar x) with
    | Some e => Some (set1 e)
    | None => None
    end.

  Fixpoint sem_setsyn (x : setsyn) : option {set T} := 
    match x with
    | FSS_empty => Some set0
    | FSS_full => Some setT
    | FSS_single e => sem_singleton e
    | FSS_var k => List.nth_error setvar_lst (nat_of_pos k - 1)
    | FSS_union a b =>
        match (sem_setsyn a), (sem_setsyn b) with
        | Some x, Some y => Some (setU x y)
        | _, _ => None
        end
    | FSS_diff a b =>
        match (sem_setsyn a), (sem_setsyn b) with
        | Some x, Some y => Some (setD x y)
        | _, _ => None
        end
    | FSS_inter a b =>
        match (sem_setsyn a), (sem_setsyn b) with
        | Some x, Some y => Some (setI x y)
        | _, _ => None
        end
    end.

  Definition sem_setelt x :=
    match x with
    | FE_var a => sem_eltvar a
    | FE_exvar a b => asn a b (* existential variable introduced by (S3) *)
    end.

  Definition sem_FSP_In (a : setelt) (A : setsyn) :=
    match (sem_setelt a), (sem_setsyn A) with
    | Some a, Some A => Some (a \in A)
    | _, _ => None
    end.

  Definition sem_FSP_Eqelt (a : setelt) (b : setelt) :=
    match (sem_setelt a), (sem_setelt b) with
    | Some x, Some y => Some (x == y)
    | _, _ => None
    end.

  Definition sem_FSP_Eqset (A : setsyn) (B : setsyn) :=
    match (sem_setsyn A), (sem_setsyn B) with
    | Some A, Some B => Some (A == B)
    | _, _ => None
    end.

  Definition sem_FSP_Sub (A : setsyn) (B : setsyn) :=
    match (sem_setsyn A), (sem_setsyn B) with
    | Some A, Some B => Some (A \subset B)
    | _, _ => None
    end.
      

  Definition sem_setpred (p : setpred) : option bool :=
    match p with
    | FSP_In a b => sem_FSP_In a b
    | FSP_Eqelt a b => sem_FSP_Eqelt a b
    | FSP_Eqset a b => sem_FSP_Eqset a b
    | FSP_Sub a b => sem_FSP_Sub a b
    end.

  Fixpoint sem_setform (f : setform) : option bool :=
    match f with
    | F_Pred p => (sem_setpred p)
    | F_Not f =>
        if (sem_setform f) is Some g then Some (~~ g) else None
    | F_And a b =>
        match (sem_setform a), (sem_setform b) with
        | Some a, Some b => Some (a && b)
        | _, _ => None
        end
    | F_Or a b =>
        match (sem_setform a), (sem_setform b) with
        | Some a, Some b => Some (a || b)
        | _, _ => None
        end
    | F_Imply a b =>
        match (sem_setform a), (sem_setform b) with
        | Some a, Some b => Some (a ==> b)
        | _, _ => None
        end
    | F_False => Some false
    | F_True => Some true
    end.

  (* check if there is an existential variable *)

  Definition elt_hasex (x y : setsyn) (e : setelt) :=
    match e with
    | FE_var _  => true
    | FE_exvar a b => (a == x) && (b == y)
    end.

  Definition pred_hasex x y (p : setpred) :=
    match p with
    | FSP_In a b => elt_hasex x y a
    | FSP_Eqelt a b => elt_hasex x y a || elt_hasex x y b
    | _ => false
    end.

  Fixpoint form_hasex x y (f : setform) :=
    match f with
    | F_Pred p => (pred_hasex x y p)
    | F_Not f => (form_hasex x y f)
    | F_And a b => (form_hasex x y a) || (form_hasex x y b)
    | F_Or a b => (form_hasex x y a) || (form_hasex x y b)
    | F_Imply a b => (form_hasex x y a) || (form_hasex x y b)
    | F_False => false
    | F_True => false
    end.

  Definition add_asn a b c :=
    fun x y =>
      match (x == a) && (y == b) with
      | true => Some c
      | false => asn x y
      end.

End setform_interp.

Section setform_decide.

  Variable T : finType.
  Variable (setvar_lst : seq {set T}).
  Variable (var_lst : seq T).

  Local Notation sem_elt := (@sem_setelt T var_lst).
  Local Notation sem_syn := (@sem_setsyn T setvar_lst var_lst).
  Local Notation sem_pred := (@sem_setpred T setvar_lst var_lst).
  Local Notation sem_form := (@sem_setform T setvar_lst var_lst).
  Definition valid_form asn f :=
    if (sem_form asn f) is Some b then b else false.

  Local Notation branch := (seq setform).
  Local Notation exasn := (setsyn -> setsyn -> option T).

  Lemma noex_sem_elt (e : setelt) x y z asn :
    ~~ elt_hasex x y e -> sem_elt (add_asn asn x y z) e = sem_elt asn e.
  Proof.
    by case: e => //= a b /negbTE H; rewrite /add_asn H.
  Qed.


  Lemma noex_sem_pred (p : setpred) x y z asn :
    ~~ pred_hasex x y p -> sem_pred (add_asn asn x y z) p = sem_pred asn p.
  Proof.
    case: p; try by [].
    - move=> a b /= H. by rewrite /sem_FSP_In noex_sem_elt.
    - move=> a b /=.
      rewrite negb_or => /andP [] /noex_sem_elt Ha /noex_sem_elt Hb.
      rewrite /sem_FSP_Eqelt Ha Hb //=.
  Qed.

  Lemma noex_sem_form (f : setform) x y z asn :
    ~~ form_hasex x y f -> sem_form (add_asn asn x y z) f = sem_form asn f.
  Proof.
    elim: f; try by move=> a Ha b Hb /=; rewrite negb_or => /andP [Pa Pb]; rewrite (Ha Pa) (Hb Pb).
    - move=> p Hp; by apply: noex_sem_pred.
    - by move=> f Hf /= /Hf ->.
    - by [].
    - by [].
  Qed.

  Lemma noex_valid_form (f : setform) x y z asn :
    ~~ form_hasex x y f -> valid_form (add_asn asn x y z) f = valid_form asn f.
  Proof.
    move/noex_sem_form => /(_ z asn). rewrite /valid_form.
    case: (sem_form _); case: (sem_form _) => //.
    by move=> ? ? [] ->.
  Qed.


  Lemma add_asnE asn a b c :
    sem_elt (add_asn asn a b c) (FE_exvar a b) = Some c.
  Proof.
    by rewrite /sem_elt /add_asn !eqxx.
  Qed.

  Notation F_NotSub a b := (F_Not (F_Pred (FSP_Sub a b))).

  Definition ext_nsub (a b : setsyn) :=
    [:: F_Pred (FSP_In (FE_exvar a b) a);
     (F_Not (F_Pred (FSP_In (FE_exvar a b) b)))].

  Lemma ext_nsub_sound a b :
    forall asn, valid_form asn (F_Not (F_Pred (FSP_Sub a b))) ->
                (exists c, all (valid_form (add_asn asn a b c)) (ext_nsub a b)).
  Proof.
    move=> asn. rewrite /valid_form /ext_nsub.
    remember (sem_form asn (F_NotSub a b)) as sf.
    case: sf Heqsf => //= ?.
    remember (sem_FSP_Sub setvar_lst var_lst a b) as sf.
    case: sf Heqsf => //= ?.
    rewrite /sem_FSP_Sub /sem_FSP_In.
    case: (sem_syn a) => // A.
    case: (sem_syn b) => // B [] -> [] ->.
    move/subsetPn=> [x xin xnin].
    exists x. by rewrite !add_asnE xin xnin.
  Qed.

  Definition is_nsub f : (prod setsyn setsyn) + (unit) :=
    match f with
    | F_Not (F_Pred (FSP_Sub a b)) => inl (a, b)
    | _ => inr tt
    end.

  (* S3 introduce existential variable *)

  Lemma is_nsubE f a b :
    (is_nsub f) = inl (a, b) -> f = (F_Not (F_Pred (FSP_Sub a b))).
  Proof.
    case: f => //=. move=> [] //= [] //= x y H.
    injection H. by move=> -> ->.
  Qed.

  Fixpoint br_ext_nsub_aux  (br res : branch) :=
    match br with
    | nil => res
    | f :: br =>
        match (is_nsub f) with
        | inl (a, b) =>
            match has (form_hasex a b) res with
            | true => br_ext_nsub_aux br res
            | false => br_ext_nsub_aux br ((ext_nsub a b) ++ res)
            end
        | inr _ => br_ext_nsub_aux br res
        end
    end.

  Lemma not_has_all_not {S : Type} f (s : seq S) :
    ~~ has f s -> all (fun x => ~~ f x) s.
  Proof.
    elim: s => //=; by move=> a s IH; rewrite negb_or => /andP [] -> /IH ->.
  Qed.

  Lemma noex_dont_change x y asn br c :
    ~~ has (form_hasex x y) br ->
    all (valid_form asn) br ->
    all (valid_form (add_asn asn x y c)) br.
  Proof.
    move=> /not_has_all_not.
    elim: br => //.
    move=> f br IH /= /andP [Hf] /IH Hbr /andP [].
    by rewrite -(noex_valid_form c asn Hf) => -> /Hbr ->.
  Qed.

  Lemma br_ext_nsub_aux_cat asn x y br:
    valid_form asn (F_Not (F_Pred (FSP_Sub x y))) ->
    ~~ has (form_hasex x y) br ->
    all (valid_form asn) br ->
    exists asn', all (valid_form asn') ((ext_nsub x y) ++ br).
  Proof.
    elim: br.
    - move=> /ext_nsub_sound [c Hc] _.
      exists (add_asn asn x y c). by [].
    - move=> f br IH /ext_nsub_sound [c Hc1].
      move=> /(@noex_dont_change x y asn (f::br) c) H /H Hc2.
      exists (add_asn asn x y c).
      by rewrite all_cat Hc1 Hc2.
  Qed.

  Lemma in_mem_all (S : eqType) P (A : seq S) x:
    x \in A -> all P A -> P x.
  Proof.
    elim: A => //. move=> a A IH. rewrite in_cons => /orP [].
    - by move=> /eqP -> /andP [].
    - by move=> {}/IH IH /andP [_] /IH.
  Qed.

  Lemma sub_mem_all {S : eqType} P (A B : seq S) :
    {subset A <= B} -> all P B -> all P A.
  Proof.
    elim: A B => //=.
    - move=> a A IH B Hsub PB.
      assert (aincons : a \in a :: A). by apply: mem_head.
      assert (ainB := Hsub _ aincons).
      rewrite (in_mem_all ainB PB).
      assert (AsB : {subset A <= B}).
    - move=> x xinA. apply: Hsub. by rewrite in_cons xinA orbT. 
      by rewrite (IH _ AsB PB).
  Qed.

  Lemma subseq_all {S : eqType} P (A B : seq S) :
    subseq A B -> all P B -> all P A.
  Proof.
    by move=> /mem_subseq /sub_mem_all; apply.
  Qed.

  Lemma br_ext_nsub_aux_subseq br res :
    subseq res (br_ext_nsub_aux br res).
  Proof.
    elim: br res.
    - by move=> res; apply: subseq_refl.
    - move=> f br IH res /=.
      case: (is_nsub f).
      + move=> [a b]. case: (has (form_hasex a b) res).
        * apply: IH.
        * eapply (subseq_trans (subseq_cons _ _)).
          eapply (subseq_trans (subseq_cons _ _)).
          apply IH.
        * move=> _; apply: IH.
  Qed.

  Lemma br_ext_nsub_aux_sound br res asn:
    subseq br res ->
    all (valid_form asn) res ->
    exists asn', all (valid_form asn') (br_ext_nsub_aux br res).
  Proof.
    elim: br res asn.
    - move=> res asn _ H; exists asn; by [].
    - move=> f br IH res asn Hbr Hres.
      change (br_ext_nsub_aux (f :: br) res) with
        match (is_nsub f) with
        | inl (a, b) =>
            match has (form_hasex a b) res with
            | true => br_ext_nsub_aux br res
            | false => br_ext_nsub_aux br ((ext_nsub a b) ++ res)
            end
        | inr _ => br_ext_nsub_aux br res
        end.
      move: (@is_nsubE f); case: (is_nsub f).
      + move=> [a b] Hab.
        move: (@br_ext_nsub_aux_cat asn a b res).
        assert (sbr : subseq br res).
        by eapply (subseq_trans (subseq_cons _ _)); apply: Hbr.
        case: (has (form_hasex a b) res).
        * move=> _; apply: IH. apply: sbr. apply: Hres.
        * move=> Hext.
          assert (allfbr : all (valid_form asn) (f :: br)).
          by apply: subseq_all; [apply: Hbr | apply: Hres].
          assert (Hf : valid_form asn f).
          by move: allfbr => /andP [].
          assert (eqf: f = (F_Not (F_Pred (FSP_Sub a b)))). by apply: Hab.
          rewrite eqf in Hf.
          move: (Hext Hf erefl Hres) => [asn' Hasn'].
          apply (IH _ asn').
          assert (sres : subseq res (ext_nsub a b ++ res)).
          by apply : suffix_subseq.
          apply (subseq_trans sbr sres).
          apply Hasn'.
      + move=> _ _. apply: IH.
        assert (H1 : subseq br (f :: br)). apply: subseq_cons.
        eapply (subseq_trans H1 Hbr).
        apply Hres.
  Qed.

  (* Eval cbv in
    (br_ext_nsub_aux [:: F_Not (F_Pred (FSP_Sub (FSS_var xH) (FSS_var xH)))]
                     [:: F_Not (F_Pred (FSP_Sub (FSS_var xH) (FSS_var xH)))]
    ). *)

  Definition br_ext_nsub br := br_ext_nsub_aux br br.

  Lemma br_ext_nsub_sound asn br :
    all (valid_form asn) br -> exists asn', all (valid_form asn') (br_ext_nsub br).
  Proof.
    move=> H.
    rewrite /br_ext_nsub.
    apply: br_ext_nsub_aux_sound. apply: subseq_refl. apply: H.
  Qed.

  (*
Definition nodup_cons {S : eqType} x (s : seq S) :=
  if (x \in s) then s else (x :: s).

Fixpoint nodup_cat {S : eqType} (a b : seq S) :=
  match a with
  | nil => b
  | x :: xs => nodup_cons x (nodup_cat xs b)
  end.

Lemma all_nodup_cons {S : eqType} (p : S -> bool) x (s : seq S) :
  p x -> all p s -> all p (nodup_cons x s).
Proof.
  elim: s.
  - by rewrite /nodup_cons => /= ->.
  - move=> a s IH IHx IHs.
    rewrite /nodup_cons.
    case: (x \in a :: s).
    + by apply IHs.
    + move=> /=.
      rewrite IHx => /=.
      change (p a && all p s) with (all p (a :: s)).
      by rewrite IHs.
Qed.

Lemma all_nodup_cat {S : eqType} (p : S -> bool) (a b : seq S) :
  all p a -> all p b -> all p (nodup_cat a b).
Proof.
  elim: a => //=.
  move=> x s IH /andP [Hx Hs] Hb.
  apply: all_nodup_cons. apply: Hx. by apply: IH.
  Qed.
   *)

  Definition all_undup {S : eqType} (p : S -> bool) (s : seq S) :
    all p (undup s) = all p s
    := (eq_all_r (mem_undup s) p).

  (* P1 P5 P6 P7 S4 S8 S9 S10 S11 S13 S14 *)

  Fixpoint ext_single (ext : setform -> seq setform) (br : branch) :=
    match br with
    | nil => nil
    | f :: fs => (ext f) ++ (ext_single ext fs)
    end.

  Definition br_ext_single ext (br : branch) :=
    (ext_single ext br) ++ br.

  Lemma ext_single_sound ext br asn :
    (forall f, (valid_form asn f) -> all (valid_form asn) (ext f)) ->
    all (valid_form asn) br -> all (valid_form asn) (ext_single ext br).
  Proof.
    move=> H.
    elim: br => //.
    move=> f br IH /andP [IHf IHbr] /=. move: (H f) => {H}.
    move=> H. by rewrite all_cat (H IHf) /= (IH IHbr).
  Qed.

  Lemma br_ext_single_sound ext br asn :
    (forall f, (valid_form asn f) -> all (valid_form asn) (ext f)) ->
    all (valid_form asn) br -> all (valid_form asn) (br_ext_single ext br).
  Proof. move=> H Hbr. by rewrite all_cat Hbr ext_single_sound. Qed.

  (* P1 *)

  Definition ext_and (f : setform) :=
    match f with
    | F_And a b => [:: a; b]
    | _ => nil
    end.

  Lemma ext_and_sound asn f :
    (valid_form asn f) -> all (valid_form asn) (ext_and f).
  Proof.
    rewrite /ext_and /valid_form. case: f => //. move=> a b /=.
    do 2 (case: (sem_form _) => //). by move=> ? ?; rewrite andbT.
  Qed.

  (* P5 *)

  Definition ext_nor (f : setform) :=
    match f with
    | F_Not (F_Or a b) => [:: F_Not a; F_Not b]
    | _ => nil
    end.

  Lemma ext_nor_sound asn f:
    (valid_form asn f) -> all (valid_form asn) (ext_nor f).
  Proof.
    rewrite /ext_nor /valid_form. case: f => //. case => //. move=> a b /=.
    do 2 (case: (sem_form _) => //). by move=> ? ?; rewrite negb_or andbT.
  Qed.

  (* P6 *)

  Definition ext_nimp (f : setform) :=
    match f with
    | F_Not (F_Imply a b) => [:: a; F_Not b]
    | _ => nil
    end.

  Lemma ext_nimp_sound asn f:
    (valid_form asn f) -> all (valid_form asn) (ext_nimp f).
  Proof.
    rewrite /ext_nor /valid_form. case: f => //. case => //. move=> a b /=.
    do 2 (case: (sem_form _) => //). by move=> ? ?; rewrite negb_imply andbT.
  Qed.

  (* P7 *)

  Definition ext_nnot(f : setform) :=
    match f with
    | F_Not (F_Not a) => [:: a]
    | _ => nil
    end.

  Lemma ext_nnot_sound asn f:
    (valid_form asn f) -> all (valid_form asn) (ext_nnot f).
  Proof.
    rewrite /ext_nor /valid_form. case: f => //. case => //. move=> f /=.
    case: (sem_form _) => //. by move=> ? /negbNE ->.
  Qed.

  (* S4 *)

  Definition ext_seteq (f : setform) :=
    match f with
    | F_Pred (FSP_Eqset a b) => [:: F_Pred (FSP_Sub a b); F_Pred (FSP_Sub b a)]
    | _ => nil
    end.

  Lemma ext_seteq_sound asn f:
    (valid_form asn f) -> all (valid_form asn) (ext_seteq f).
  Proof.
    rewrite /ext_seteq /valid_form. case: f => //. case=> //.
    move=> a b /=. rewrite /sem_FSP_Eqset /sem_FSP_Sub.
    case: (sem_syn _) => //; case: (sem_syn _) => //.
    move=> ? ? /eqP ->. by rewrite !subxx.
  Qed.

  (* S8 *)

  Definition ext_elteq (f : setform) :=
    match f with
    | F_Pred (FSP_Eqelt a b) => [:: F_Pred (FSP_Eqelt b a)]
    | _ => nil
    end.

  Lemma ext_elteq_sound asn f:
    (valid_form asn f) -> all (valid_form asn) (ext_elteq f).
  Proof.
    rewrite /ext_elteq /valid_form. case: f => //. case=> //.
    move=> a b /=. rewrite /sem_FSP_Eqelt.
    case: (sem_elt asn a); case: (sem_elt asn b) => //.
    move=> x y /eqP ->; by rewrite eqxx.
  Qed.

  (* S9 *)

  Definition ext_insingle (f : setform) :=
    match f with
    | F_Pred (FSP_In a (FSS_single b)) => [:: F_Pred (FSP_Eqelt a (FE_var b))]
    | _ => nil
    end.

  Lemma ext_insingle_sound asn f:
    (valid_form asn f) -> all (valid_form asn) (ext_insingle f).
  Proof.
    rewrite /ext_insingle /valid_form. case: f => //. case=> //=.
    move=> a. case=> // b /=.
    rewrite /sem_FSP_In /sem_FSP_Eqelt. case: (sem_elt asn a) => //= x.
    rewrite /sem_singleton. case: (sem_eltvar _) => // y.
    by rewrite in_set1 => ->.
  Qed.

  (* S10 *)

  Definition ext_ninsingle (f : setform) :=
    match f with
    | F_Not (F_Pred (FSP_In a (FSS_single b))) =>
        [:: F_Not (F_Pred (FSP_Eqelt a (FE_var b)))]
    | _ => nil
    end.

  Lemma ext_ninsingle_sound asn f:
    (valid_form asn f) -> all (valid_form asn) (ext_ninsingle f).
  Proof.
    rewrite /ext_insingle /valid_form. case: f => //. case=>//=. case=>//=.
    move=> a. case=> // b /=.
    rewrite /sem_FSP_In /sem_FSP_Eqelt. case: (sem_elt asn a) => //= x.
    rewrite /sem_singleton. case: (sem_eltvar _) => // y.
    by rewrite in_set1 => ->.
  Qed.

  (* S11 *)

  Definition ext_singlesub (f : setform) :=
    match f with
    | (F_Pred (FSP_Sub (FSS_single a) b)) => [:: (F_Pred (FSP_In (FE_var a) b))]
    | _ => nil
    end.

  Lemma ext_singlesub_sound asn f:
    (valid_form asn f) -> all (valid_form asn) (ext_singlesub f).
  Proof.
    rewrite /ext_singlesub /valid_form. case: f => //. case=> //. case=> //.
    move=> a b /=. rewrite /sem_FSP_Sub /= /sem_FSP_In /sem_singleton /sem_elt.
    case: (sem_eltvar var_lst a) => // x. case: (sem_syn _) => // B.
    by rewrite sub1set => ->.
  Qed.

  (* S13 *)

  Definition ext_ninunion (f : setform) :=
    match f with
    | F_Not (F_Pred (FSP_In a (FSS_union b c))) =>
        [:: F_Not (F_Pred (FSP_In a b)); F_Not (F_Pred (FSP_In a c))]
    | _ => nil
    end.

  Lemma ext_ninunion_sound asn f:
    (valid_form asn f) -> all (valid_form asn) (ext_ninunion f).
  Proof.
    rewrite /ext_ninunion /valid_form. case: f => //. case=> //. case=> //.
    move=> a. case=> // b c /=.
    rewrite /sem_FSP_In. case: (sem_elt asn a) => // x /=.
    case: (sem_syn _) => // B. case: (sem_syn _) => // C.
    by rewrite in_setU negb_or => /andP [] -> ->.
  Qed.

  (* S14 *)

  Definition ext_indiff (f : setform) :=
    match f with
    | (F_Pred (FSP_In a (FSS_diff b c))) =>
        [:: (F_Pred (FSP_In a b)); F_Not (F_Pred (FSP_In a c))]
    | _ => nil
    end.

  Lemma ext_indiff_sound asn f:
    (valid_form asn f) -> all (valid_form asn) (ext_indiff f).
  Proof.
    rewrite /ext_indiff /valid_form. case: f => // [] // [] //.
    move=> a. case=> // b c /=.
    rewrite /sem_FSP_In. case: (sem_elt asn a) => // {a} x /=.
    case: (sem_syn _) => // B. case: (sem_syn _) => // C.
    by rewrite in_setD => /andP [] -> ->.
  Qed.

  (* S16 in_setI *)

  Definition ext_ininter (f : setform) :=
    match f with
    | (F_Pred (FSP_In a (FSS_inter b c))) =>
        [:: (F_Pred (FSP_In a b)); (F_Pred (FSP_In a c))]
    | _ => nil
    end.

  Lemma ext_ininter_sound asn f:
    (valid_form asn f) -> all (valid_form asn) (ext_ininter f).
  Proof.
    rewrite /ext_ininter /valid_form. case: f => // [] // [] //.
    move=> a. case=> // b c /=.
    rewrite /sem_FSP_In. case: (sem_elt asn a) => // {a} ? /=.
    case: (sem_syn _) => // B. case: (sem_syn _) => // C.
    by rewrite in_setI => /andP [] -> ->.
  Qed.

  (* all single premise extension *)

  Definition br_ext_single_all br :=
    let br := (br_ext_single ext_and br) in
    let br := (br_ext_single ext_nor br) in
    let br := (br_ext_single ext_nimp br) in
    let br := (br_ext_single ext_nnot br) in
    let br := (br_ext_single ext_seteq br) in
    let br := (br_ext_single ext_elteq br) in
    let br := (br_ext_single ext_insingle br) in
    let br := (br_ext_single ext_ninsingle br) in
    let br := (br_ext_single ext_singlesub br) in
    let br := (br_ext_single ext_ninunion br) in
    let br := (br_ext_single ext_indiff br) in
    let br := (br_ext_single ext_ininter br) in
    br.

  Lemma br_ext_single_all_sound asn br :
    all (valid_form asn) br -> all (valid_form asn) (br_ext_single_all br).
  Proof.
    move=> H.
    rewrite /br_ext_single_all.
    apply: (br_ext_single_sound (@ext_ininter_sound _)).
    apply: (br_ext_single_sound (@ext_indiff_sound _)).
    apply: (br_ext_single_sound (@ext_ninunion_sound _)).
    apply: (br_ext_single_sound (@ext_singlesub_sound _)).
    apply: (br_ext_single_sound (@ext_ninsingle_sound _)).
    apply: (br_ext_single_sound (@ext_insingle_sound _)).
    apply: (br_ext_single_sound (@ext_elteq_sound _)).
    apply: (br_ext_single_sound (@ext_seteq_sound _)).
    apply: (br_ext_single_sound (@ext_nnot_sound _)).
    apply: (br_ext_single_sound (@ext_nimp_sound _)).
    apply: (br_ext_single_sound (@ext_nor_sound _)).
    apply: (br_ext_single_sound (@ext_and_sound _)).
    exact: H.
  Qed.

  (* nonbranching rules with two premises *)
  (* S1 S2 S6 S7 *)

  Fixpoint ext_pair
           (ext : (setform * setform) -> seq setform)
           (ps : seq (setform * setform)) :=
    match ps with
    | nil => nil
    | p :: ps => (ext p) ++ (ext_pair ext ps)
    end.

  Definition br_ext_pair ext br :=
    (ext_pair ext (List.list_prod br br)) ++ br.

  Lemma ext_pair_sound asn ext ps :
    (forall p, (valid_form asn (fst p) && valid_form asn (snd p)) ->
               all (valid_form asn) (ext p)) ->
    all (fun p => (valid_form asn (fst p)) && (valid_form asn (snd p))) ps ->
    all (valid_form asn) (ext_pair ext ps).
  Proof.
    elim: ps => //.
    move=> p ps IH Hext /= /andP [Hsem Hps].
    by rewrite all_cat (Hext _ Hsem) (IH Hext Hps).
  Qed.

  Lemma List_In_in_mem {S : eqType} a (s : seq S) :
    List.In a s <-> a \in s.
  Proof.
    rewrite /iff. split.
    - elim: s => //. move=> x s IH H. move: (List.in_inv H) => [].
      + by rewrite in_cons => ->; rewrite eqxx.
      + by rewrite in_cons => /IH ->; rewrite orbT.
    - elim: s => //. move=> x s IH. rewrite in_cons => /orP [].
      + move=> /eqP -> //=. by left.
      + move=> /IH //=. by right.
  Qed.

  Lemma br_ext_pair_sound asn ext br:
    (forall p, (valid_form asn (fst p) && valid_form asn (snd p)) ->
               all (valid_form asn) (ext p)) ->
    all (valid_form asn) br ->
    all (valid_form asn) (br_ext_pair ext br).
  Proof.
    move=> Hext Hbr. rewrite all_cat Hbr andbT ext_pair_sound => //.
    apply/allP=> p. move: p => [p1 p2].
    rewrite -List_In_in_mem List.in_prod_iff !List_In_in_mem.
    move=> [Hp1 Hp2].
    by rewrite (in_mem_all Hp1 Hbr) (in_mem_all Hp2 Hbr).
  Qed.

  (* S1 *)
  Definition ext_insub (p : setform * setform):=
    let (p1, p2) := p in
    match p1, p2 with
    | F_Pred (FSP_In a A), (F_Pred (FSP_Sub A' B)) =>
        if A == A' then [:: F_Pred (FSP_In a B)] else nil
    | _, _ => nil
    end.

  Lemma ext_insub_sound asn p :
    valid_form asn (fst p) && valid_form asn (snd p) ->
    all (valid_form asn) (ext_insub p).
  Proof.
    move: p => [p1 p2]. rewrite /ext_insub /valid_form /=.
    case: p1 => //. case => //= => a A. case: p2 => //. case => //= => A' B.
    rewrite /sem_FSP_In /sem_FSP_Sub.
    remember (A == A') as eqA.
    move: HeqeqA. case: eqA => //= /esym /eqP <-. rewrite /sem_FSP_In.
    case: (sem_elt _) => // x.
    case: (sem_syn _) => // X. case: (sem_syn _) => //; last by rewrite andbF.
    move=> Y /andP [] xin /subsetP /(_ x xin). by rewrite andbT.
  Qed.

  (* S2 *)
  Definition ext_ninsub (p : setform * setform):=
    let (p1, p2) := p in
    match p1, p2 with
    | F_Not (F_Pred (FSP_In a A)), (F_Pred (FSP_Sub B A')) =>
        if A == A' then [:: F_Not (F_Pred (FSP_In a B))] else nil
    | _, _ => nil
    end.

  Lemma ext_ninsub_sound asn p :
    valid_form asn (fst p) && valid_form asn (snd p) ->
    all (valid_form asn) (ext_ninsub p).
  Proof.
    move: p => [p1 p2]. rewrite /ext_ninsub /valid_form /=.
    case: p1 => //. case => //.
    case => //= => a A. case: p2 => //. case => //= => B A'.
    rewrite /sem_FSP_In /sem_FSP_Sub.
    remember (A == A') as eqA.
    move: HeqeqA. case: eqA => //= /esym /eqP <-. rewrite /sem_FSP_In.
    case: (sem_elt _) => // x.
    case: (sem_syn _) => // X. case: (sem_syn _) => //; last by rewrite andbF.
    move=> Y /andP [] xnin HYX. rewrite andbT. move: xnin. apply: contraNN.
    by move=> xin; move: HYX => /subsetP /(_ _ xin).
  Qed.

  (* S6 *)
  Definition ext_eqin (p : setform * setform):=
    let (p1, p2) := p in
    match p1, p2 with
    | (F_Pred (FSP_Eqelt a b)), (F_Pred (FSP_In b' B)) =>
        if b == b' then [:: (F_Pred (FSP_In a B))] else nil
    | _, _ => nil
    end.

  Lemma ext_eqin_sound asn p :
    valid_form asn (fst p) && valid_form asn (snd p) ->
    all (valid_form asn) (ext_eqin p).
  Proof.
    move: p => [p1 p2]. rewrite /ext_eqin /valid_form.
    case: p1 => //. case=> //= a0 b0.
    case: p2 => //. case=> //= b'0 B.
    case: (@eqP _ b0 b'0) => // <- /=.
    rewrite /sem_FSP_Eqelt /sem_FSP_In.
    case: (sem_elt asn a0) => // a.
    case: (sem_elt asn b0) => // b.
    case: (sem_syn _) => //; last by rewrite andbF.
    move=> Y /andP [] /eqP ->. by rewrite andbT.
  Qed.

  (* S7 *)
  Definition ext_eqtrans (p : setform * setform):=
    let (p1, p2) := p in
    match p1, p2 with
    | (F_Pred (FSP_Eqelt a b)), (F_Pred (FSP_Eqelt b' c)) =>
        if b == b' then [:: (F_Pred (FSP_Eqelt a c))] else nil
    | _, _ => nil
    end.

  Lemma ext_eqtrans_sound asn p :
    valid_form asn (fst p) && valid_form asn (snd p) ->
    all (valid_form asn) (ext_eqtrans p).
  Proof.
    move: p => [p1 p2]. rewrite /ext_eqin /valid_form.
    case: p1 => //. case=> //= a0 b0.
    case: p2 => //. case=> //= b'0 b.
    case: (@eqP _ b0 b'0) => // <- /=.
    rewrite /sem_FSP_Eqelt /sem_FSP_In.
    case: (sem_elt asn a0) => // x.
    case: (sem_elt asn b0) => // y.
    case: (sem_elt _) => //; last by rewrite andbF.
    move=> Y /andP [] /eqP -> /eqP ->. by rewrite eqxx.
  Qed.

  Definition br_ext_pair_all br :=
    let br := br_ext_pair ext_insub br in
    let br := br_ext_pair ext_ninsub br in
    let br := br_ext_pair ext_eqin br in
    let br := br_ext_pair ext_eqtrans br in
    br.

  Lemma br_ext_pair_all_sound asn br :
    all (valid_form asn) br -> all (valid_form asn) (br_ext_pair_all br).
  Proof.
    move=> H.
    rewrite /br_ext_pair_all.
    apply: (br_ext_pair_sound (@ext_eqtrans_sound _)).
    apply: (br_ext_pair_sound (@ext_eqin_sound _)).
    apply: (br_ext_pair_sound (@ext_ninsub_sound _)).
    apply: (br_ext_pair_sound (@ext_insub_sound _)).
    exact: H.
  Qed.

  (* branching rules *)
  (* P2 P3 P4 S5 S12 S15 S17 *)

  (* Eval compute in (1 \in [:: 1; 2; 3]). *)

  Fixpoint get_form_branching_aux
           (ext : setform -> option (setform * setform))
           (fs br : branch) :=
    match fs with
    | nil => None
    | f :: fs =>
        match (ext f) with
        | Some (a, b) =>
            match ((a \in br) || (b \in br)) with
            | true => get_form_branching_aux ext fs br
            | false => Some (a, b)
            end
        | None => get_form_branching_aux ext fs br
        end
    end.

  Lemma get_form_branching_aux_sound asn ext fs br:
    (forall f a b, ext f = Some (a, b) -> valid_form asn f -> 
                   valid_form asn a || valid_form asn b) ->
    all (valid_form asn) fs ->
    forall a b, get_form_branching_aux ext fs br = Some (a, b) ->
                valid_form asn a || valid_form asn b.
  Proof.
    move=> Hext.
    elim: fs => //.
    move=> f fs IH /= /andP [Hf Hfs] a b.
    move: (Hext f) => /=.
    case: (ext f); last by move=> _; apply: (IH Hfs).
    move=> [a0 b0] H /=.
    case: ((a0 \in br) || (b0 \in br)); first by apply: (IH Hfs a b).
    move=> [] <- <-. by apply: (H a0 b0 _ Hf).
  Qed.

  Definition get_form_branching ext br :=
    get_form_branching_aux ext br br.

  Lemma get_form_branching_sound asn ext br:
    (forall f a b, ext f = Some (a, b) -> valid_form asn f -> 
                   valid_form asn a || valid_form asn b) ->
    all (valid_form asn) br ->
    forall a b, get_form_branching ext br = Some (a, b) ->
                valid_form asn a || valid_form asn b.
  Proof.
    move=> H Hbr. rewrite /get_form_branching.
    by apply: get_form_branching_aux_sound.
  Qed.

  (* P2 *)

  Definition ext_or f :=
    match f with
    | F_Or a b => Some (a, b)
    | _ => None
    end.

  Lemma ext_or_sound asn f a b :
    ext_or f = Some (a, b) -> valid_form asn f -> valid_form asn a || valid_form asn b.
  Proof.
    case: f => //. move=> x y /= [] -> ->. rewrite /valid_form /=.
    by case: (sem_form _) => //; case: (sem_form _) => //.
  Qed.

  (* P3 *)

  Definition ext_imp f :=
    match f with
    | F_Imply a b => Some (F_Not a, b)
    | _ => None
    end.

  Lemma ext_imp_sound asn f a b :
    ext_imp f = Some (a, b) -> valid_form asn f ->
    valid_form asn a || valid_form asn b.
  Proof.
    case: f => //. move=> a0 b0 /= [] <- <- /=.
    rewrite /valid_form /=. case: (sem_form _) => //. case: (sem_form _) => //.
    by move=> x y; rewrite implybE.
  Qed.

  (* P4 *)

  Definition ext_nand f :=
    match f with
    | F_Not (F_And a b) => Some (F_Not a, F_Not b)
    | _ => None
    end.

  Lemma ext_nand_sound asn f a b :
    ext_nand f = Some (a, b) -> valid_form asn f ->
    valid_form asn a || valid_form asn b.
  Proof.
    case: f => //. case => //. move=> a0 b0 /= [] <- <- /=.
    rewrite /valid_form /=. case: (sem_form _) => //. case: (sem_form _) => //.
    by move=> x y; rewrite negb_and.
  Qed.

  (* S5 *)

  Definition ext_setneq f :=
    match f with
    | F_Not (F_Pred (FSP_Eqset a b)) =>
        Some (F_Not (F_Pred (FSP_Sub a b)), F_Not (F_Pred (FSP_Sub b a)))
    | _ => None
    end.

  Lemma ext_setneq_sound asn f a b :
    ext_setneq f = Some (a, b) -> valid_form asn f ->
    valid_form asn a || valid_form asn b.
  Proof.
    case: f => //. case => //. case => //. move=> a0 b0 /= [] <- <- /=.
    rewrite /valid_form /= /sem_FSP_Eqset /sem_FSP_Sub.
    case: (sem_syn _) => //. case: (sem_syn _) => //.
    by move=> x y; rewrite eqEsubset negb_and.
  Qed.

  (* S12 *)

  Definition ext_inunion f :=
    match f with
    | (F_Pred (FSP_In x (FSS_union A B))) =>
        Some ((F_Pred (FSP_In x A)), (F_Pred (FSP_In x B)))
    | _ => None
    end.

  Lemma ext_inunion_sound asn f a b :
    ext_inunion f = Some (a, b) -> valid_form asn f ->
    valid_form asn a || valid_form asn b.
  Proof.
    case: f => //. case => //. move=> x. case => //.
    move=> a0 b0 /= [] <- <- /=.
    rewrite /valid_form /= /sem_FSP_In /=. case: (sem_elt asn x) => // y.
    case: (sem_syn _) => //. case: (sem_syn _) => //.
    by move=> c d; rewrite in_setU.
  Qed.

  (* S15 *)

  Definition ext_nindiff f :=
    match f with
    | F_Not (F_Pred (FSP_In x (FSS_diff A B))) =>
        Some (F_Not (F_Pred (FSP_In x A)), (F_Pred (FSP_In x B)))
    | _ => None
    end.

  Lemma ext_nindiff_sound asn f a b :
    ext_nindiff f = Some (a, b) -> valid_form asn f ->
    valid_form asn a || valid_form asn b.
  Proof.
    case: f => //. case => //. case => //. move=> x. case => //.
    move=> a0 b0 /= [] <- <- /=. rewrite /valid_form /= /sem_FSP_In /=.
    case: (sem_elt asn x) => // y.
    case: (sem_syn _) => //. case: (sem_syn _) => //.
    by move=> c d; rewrite in_setD negb_and Bool.negb_involutive orbC.
  Qed.

  (* S17 *)

  Definition ext_nininter f :=
    match f with
    | F_Not (F_Pred (FSP_In x (FSS_inter A B))) =>
        Some (F_Not (F_Pred (FSP_In x A)), F_Not (F_Pred (FSP_In x B)))
    | _ => None
    end.

  Lemma ext_nininter_sound asn f a b :
    ext_nininter f = Some (a, b) -> valid_form asn f ->
    valid_form asn a || valid_form asn b.
  Proof.
    case: f => //. case => //. case => //. move=> x. case => //.
    move=> a0 b0 /= [] <- <- /=. rewrite /valid_form /= /sem_FSP_In /=.
    case: (sem_elt asn x) => // y.
    case: (sem_syn _) => //. case: (sem_syn _) => //.
    by move=> c d; rewrite in_setI negb_and orbC.
  Qed.

  Fixpoint pick_some {A B : Type} (f : A -> option B) (s : seq A) :=
    match s with
    | nil => None
    | x :: xs =>
        match (f x) with
        | Some b => Some b
        | None => pick_some f xs
        end
    end.

  Definition br_branching br :=
    pick_some (fun f => (get_form_branching f br))
              [:: ext_or; ext_imp; ext_nand; ext_setneq; ext_inunion;
               ext_nindiff; ext_nininter].


  Lemma br_branching_sound asn br :
    all (valid_form asn) br ->
    forall a b, br_branching br = Some (a, b) ->
                valid_form asn a || valid_form asn b.
  Proof.
    move=> Hbr a b.
    rewrite /br_branching /=.
    move: (get_form_branching_sound (@ext_or_sound _) Hbr).
    case: (get_form_branching ext_or br); first by case => ? ?; apply.
    move=> _; move: (get_form_branching_sound (@ext_imp_sound _) Hbr).
    case: (get_form_branching ext_imp br); first by case => ? ?; apply.
    move=> _; move: (get_form_branching_sound (@ext_nand_sound _) Hbr).
    case: (get_form_branching ext_nand br); first by case => ? ?; apply.
    move=> _; move: (get_form_branching_sound (@ext_setneq_sound _) Hbr).
    case: (get_form_branching ext_setneq br); first by case => ? ?; apply.
    move=> _; move: (get_form_branching_sound (@ext_inunion_sound _) Hbr).
    case: (get_form_branching ext_inunion br); first by case => ? ?; apply.
    move=> _; move: (get_form_branching_sound (@ext_nindiff_sound _) Hbr).
    case: (get_form_branching ext_nindiff br); first by case => ? ?; apply.
    move=> _; move: (get_form_branching_sound (@ext_nininter_sound _) Hbr).
    case: (get_form_branching ext_nininter br); first by case => ? ?; apply.
    by [].
  Qed.

  (* closing branches *)

  Lemma cons_br_branching asn br :
    all (valid_form asn) br ->
    forall a b, br_branching br = Some (a, b) ->
                all (valid_form asn) (a :: br) || all (valid_form asn) (b :: br).
  Proof.
    move=> Hbr a b Hab.
    move: (br_branching_sound Hbr Hab) => /orP [].
    - by move=> /= ->; rewrite Hbr => /=.
    - by move=> /= ->; rewrite Hbr orbT.
  Qed.

  Fixpoint br_contra (br : branch) :=
    match br with
    | nil => false
    | f :: fs => has (fun x => (x == F_Not f) || (F_Not x == f)) fs
                 || br_contra fs
    end.

  Lemma all_false {S : eqType} x (s : seq S) p :
    (x \in s) && ~~ (p x) -> ~~ (all p s).
  Proof.
    move=> H. rewrite -has_predC.
    apply/hasP. exists x; by move: H => /andP [].
  Qed.

  Lemma all_contra {S : eqType} (s : seq S) f x y :
    (x \in s) && (y \in s) && (f x == ~~ f y) ->
    ~~ (all f s).
  Proof.
    remember (f x) as fx. move: fx Heqfx. case.
    - move=> eqfx /andP [] /andP [_ Hy] Hfy.
      apply (@all_false _ y). move: Hfy => /eqP <-. by rewrite Hy.
    - move=> eqfx /andP [] /andP [Hx _] _.
      apply (@all_false _ x). by rewrite -eqfx Hx.
  Qed.

  Lemma br_contra_sound_aux br :
    br_contra br ->
    exists x y, (x \in br) && (y \in br) && (x == (F_Not y)).
  Proof.
    elim: br => //.
    move=> f br IH /orP [].
    - move=> /hasP [x xin] /orP [Hx | Hx].
      + exists x. exists f.
        by rewrite in_cons xin orbT mem_head /=.
      + exists f. exists x.
        by rewrite !in_cons xin eqxx orbT /= eq_sym.
    - move=> /IH [x [y]] /andP [] /andP [] xin yin H. exists x. exists y.
      by rewrite !in_cons xin yin H !orbT.
  Qed.

  Lemma br_contra_sound br asn :
    br_contra br -> ~~ all (valid_form asn) br.
  Proof.
    move=> /br_contra_sound_aux [x [y]] /andP [] /andP [] xin yin /eqP eqx.
    move: (@all_contra _ br (valid_form asn) x y).
    move: (@all_false _ y br (valid_form asn)).
    rewrite /valid_form eqx /=.
    case: (sem_form asn y) => //=; last by rewrite yin => /= /(_ erefl).
    move=> b _; rewrite yin /=.
    by rewrite -eqx xin eqxx => /(_ erefl). 
  Qed.


  Definition is_in_empty (f : setform) :=
    match f with
    | F_Pred (FSP_In x FSS_empty) => true
    | _ => false
    end.

  Lemma in_empty_false asn f :
    is_in_empty f -> ~~ valid_form asn f.
  Proof.
    case: f => //. case => //. move=> x. case => //= _.
    rewrite /valid_form /= /sem_FSP_In.
    case: (sem_elt asn x) => //= => a.
    by rewrite in_set0.
  Qed.

  Lemma br_has_in_empty_contra asn br :
    has is_in_empty br -> ~~ (all (valid_form asn) br).
  Proof.
    move=> /hasP [] f finbr /in_empty_false Hf.
    apply: (@all_false _ f).
    rewrite finbr. by rewrite (Hf asn).
  Qed.

  (* Eval cbv in 
    (has is_in_empty 
         [:: F_Pred (FSP_In (FE_var xH) FSS_empty)]). *)

  Definition is_nin_full (f : setform) :=
    match f with
    | F_Not (F_Pred (FSP_In a FSS_full)) => true
    | _ => false
    end.

  Lemma nin_full_false asn f :
    is_nin_full f -> ~~ valid_form asn f.
  Proof.
    case: f => //. case => //. case => //. case => //.
    - move=> a. case=> //= _.
      rewrite /valid_form /= /sem_FSP_In /sem_elt.
      case: (sem_eltvar var_lst a) => //=.
      move=> x. apply/negPn => /=. by rewrite in_setT.
    - move=> A B. case=> //= _.
      rewrite /valid_form /= /sem_FSP_In /sem_elt.
      case: (asn _) => //=.
      move=> x. apply/negPn => /=. by rewrite in_setT.
  Qed.

  Lemma br_has_nin_full_contra asn br :
    has is_nin_full br -> ~~ (all (valid_form asn) br).
  Proof.
    move=> /hasP [] f finbr /nin_full_false Hf.
    apply: (@all_false _ f).
    rewrite finbr. by rewrite (Hf asn).
  Qed.
  
  Definition is_neg_refl (f : setform) :=
    match f with
    | F_Not (F_Pred (FSP_Eqelt a b)) => a == b
    | _ => false
    end.
  
  Lemma neg_refl_false asn f :
    is_neg_refl f -> ~~ valid_form asn f.
  Proof.
    case: f => //. case => //. case => //.
    move=> a b. rewrite /is_neg_refl => /= /eqP ->.
    rewrite /valid_form /= /sem_FSP_Eqelt /sem_elt.
    case: b => /=.
    - move=> x. case: (sem_eltvar _) => // y. by rewrite eqxx.
    - move=> A B. case: (asn _) => // y. by rewrite eqxx.
  Qed.

  Lemma br_has_neg_refl_contra asn br :
    has is_neg_refl br -> ~~ (all (valid_form asn) br).
  Proof.
    move=> /hasP [] f finbr /neg_refl_false Hf.
    apply: (@all_false _ f).
    rewrite finbr. by rewrite (Hf asn).
  Qed.

  Definition close_branch (br : branch) :=
    match (br_contra br) || (has is_in_empty br) || (has is_nin_full br)
          || (has is_neg_refl br) with
    | true => [:: F_False]
    | false => br
    end.

  (* Eval cbv in
    (close_branch
       [:: F_Not (F_Pred (FSP_Eqset (FSS_var xH) (FSS_var xH)));
        (F_Pred (FSP_Eqset (FSS_var xH) (FSS_var xH)))]). *)
  
  (* Eval cbv in
    (close_branch
       [:: F_Pred (FSP_In (FE_var xH) FSS_empty)]). *)

  Definition is_closed_branch (br : branch) :=
    match br with
    | [:: F_False] => true
    | _ => false
    end.

  Lemma is_closed_branchE br :
    is_closed_branch br -> br = [:: F_False].
  Proof.
    rewrite /is_closed_branch. case: br => //. case => //. by case.
  Qed.

  Lemma close_branch_sound br asn :
    all (valid_form asn) br -> all (valid_form asn) (close_branch br).
  Proof.
    move=> Hbr. rewrite /close_branch.
    move: (@br_contra_sound br asn).
    case: (br_contra br) => //; first by move=> /(_ erefl); rewrite Hbr.

    move=> _; move: (@br_has_in_empty_contra asn br).
    case: (has is_in_empty br) => //=; first by move=> /(_ erefl); rewrite Hbr.

    move=> _; move: (@br_has_nin_full_contra asn br).
    case: (has is_nin_full br) => //=; first by move=> /(_ erefl); rewrite Hbr.

    move=> _; move: (@br_has_neg_refl_contra asn br).
    case: (has is_neg_refl br) => //=; by move=> /(_ erefl); rewrite Hbr.
  Qed.

  Inductive has_valid_branch : seq branch -> Prop :=
  | HVB_one br asn :
    all (valid_form asn) br -> forall brs, has_valid_branch (br :: brs)
  | HVB_cons br brs : has_valid_branch brs -> has_valid_branch (br :: brs).

  Definition remove_closed_branch brs : seq branch :=
    match brs with
    | nil => nil
    | br :: brs =>
        if (is_closed_branch br)
        then brs
        else br :: brs
    end.

  Lemma remove_closed_branch_sound brs :
    has_valid_branch brs -> has_valid_branch (remove_closed_branch brs).
  Proof.
    case => //.
    - move=> br asn H bs.
      rewrite /remove_closed_branch.
      move: (@is_closed_branchE br).
      case: (is_closed_branch br);
        first by move=> /(_ erefl) eqbr; move: eqbr H => -> //=.
      move=> _; apply: HVB_one. exact: H.
    - move=> br bs H.
      rewrite /remove_closed_branch.
      case: (is_closed_branch br); first exact: H.
      apply: HVB_cons; exact: H.
  Qed.

  (* Eval cbv in (remove_closed_branch [:: [:: F_False]; [:: F_False; F_False]]). *)

  Definition br_ext_nonbranching br :=
    let newbr := br_ext_nsub br in
    let newbr := br_ext_single_all newbr in
    let newbr := br_ext_pair_all newbr in
    let newbr := undup newbr in
    let newbr := close_branch newbr in
    newbr.


  Lemma br_ext_nonbranching_sound asn br :
    all (valid_form asn) br ->
    exists asn', all (valid_form asn') (br_ext_nonbranching br).
  Proof.
    move=> H.
    assert (Hnsub : exists asn', all (valid_form asn') (br_ext_nsub br))
      by apply: br_ext_nsub_sound H.
    move: Hnsub => [asn' Hasn'].
    exists asn'.
    rewrite /br_ext_nonbranching.
    apply: close_branch_sound.
    rewrite all_undup.
    apply: br_ext_pair_all_sound.
    by apply: br_ext_single_all_sound.
  Qed.

  Fixpoint saturate
           (n : nat)
           (brs : seq branch) :=
    match n with
    | O => brs
    | S n => 
        match brs with
        | nil => nil
        | br :: brs =>
            let newbr := br_ext_nonbranching br in
            if newbr == br
            then
              match br_branching br with
              | Some (a, b) => saturate n ((a :: br) :: (b :: br) :: brs)
              | None => br :: brs
              end
            else saturate n (remove_closed_branch (newbr :: brs))
        end
    end.

  Lemma saturate_Sn_brbrs n br brs :
    saturate (S n) (br :: brs) = 
      let newbr := br_ext_nonbranching br in
      if newbr == br
      then
        match br_branching br with
        | Some (a, b) => saturate n ((a :: br) :: (b :: br) :: brs)
        | None => br :: brs
        end
      else saturate n (remove_closed_branch (newbr :: brs)).
  Proof. reflexivity. Qed.

  Lemma saturate_sound n brs :
    has_valid_branch brs -> has_valid_branch (saturate n brs).
  Proof.
    elim: n brs => //.
    move=> n IH brs Hbrs.
    case: Hbrs.
    - move=> br asn Hbr bs.
      rewrite saturate_Sn_brbrs.
      rewrite (lock br_ext_nonbranching).
      cbv zeta.
      case: (locked br_ext_nonbranching br == br).
      + move: (cons_br_branching Hbr).
        case: (br_branching br); last by move=> _; apply: (HVB_one Hbr).
        move=> [a b] /(_ a b erefl) /orP [].
        * move=> Ha. apply IH. apply: (HVB_one Ha). 
        * move=> Hb. apply IH. apply: HVB_cons. apply: (HVB_one Hb). 
      + apply: IH. apply: remove_closed_branch_sound.
        assert (Hbr' := (br_ext_nonbranching_sound Hbr)).
        move: Hbr' => [asn' Hasn']. apply: HVB_one.
        rewrite -lock. apply: Hasn'.
    - move=> br bs Hbs.
      rewrite saturate_Sn_brbrs.
      rewrite (lock br_ext_nonbranching).
      cbv zeta.
      case: (locked br_ext_nonbranching br == br).
      + case: (br_branching br).
        * move=> [a b]. apply: IH. apply: HVB_cons. by apply: HVB_cons. 
        * by apply: HVB_cons.
      + apply: IH. apply: remove_closed_branch_sound. by apply: HVB_cons.
  Qed.


  Lemma has_not_valid_branch_nil :
    ~ has_valid_branch nil. 
  Proof. move=> H. inversion H. Qed.

  Lemma valid_formNN f asn :
    forall b, Some b = sem_form asn f ->
    ~~ (valid_form asn (F_Not f)) -> valid_form asn f.
  Proof.
    move=> b. rewrite /valid_form => /= <-. by apply: negbNE. Qed.

  Lemma has_not_valid_branch_single f asn :
    ~ has_valid_branch [:: [:: f]] -> ~~ (valid_form asn f).
  Proof.
    move=> H. apply/negP. 
    have g : valid_form asn f -> has_valid_branch [:: [:: f]]
      by move=> Hbr; apply: (@HVB_one [:: f] asn) => /=; rewrite Hbr.
    by move=> /g /H.
  Qed.

  Lemma saturate_has_not_valid_branch n f :
    saturate n [:: [:: f]] == nil -> ~ has_valid_branch [:: [:: f]].
  Proof.
    move=> /eqP H hvb. move: (saturate_sound n hvb).
    rewrite H. apply: has_not_valid_branch_nil.
  Qed.

  Definition set_decide asn n f :=
    match (sem_form asn f) with
    | Some _ => saturate n [:: [:: F_Not f]] == nil
    | None => false
    end.

  Lemma set_decide_sound n f asn :
    set_decide asn n f -> valid_form asn f.
  Proof.
    rewrite /set_decide /valid_form.
    remember (sem_form asn f) as sf.
    case: sf Heqsf => // a Ha.
    move=> /saturate_has_not_valid_branch /has_not_valid_branch_single.
    move=> /(_ asn) /(valid_formNN Ha).
    by rewrite /valid_form -Ha.
  Qed.

End setform_decide.

Example E0 (T : finType) (A B : {set T}) {x y : T} asn :
  valid_form [:: A; B] [:: x; y] asn
               (F_Pred (FSP_Sub (FSS_var (xO xH)) (FSS_var xH)))
  =
    (B \subset A).
Proof.
  by [].
Qed.

Example E1 (T : finType) (A B : {set T}) {x y : T} asn :
  valid_form [:: A; B] [:: x; y] asn
               (F_Pred (FSP_Eqset (FSS_var (xO xH)) (FSS_var xH)))
  =
    (B == A).
Proof.
  by [].
Qed.

(* rewrite Props to boolean expressions *)

Global Hint Rewrite <- setTD setI_eq0 : setdec_unfold.

Lemma rwPeqP (T : eqType) (x y : T) : x = y <-> x == y.
Proof. by rewrite (rwP eqP). Qed.

Lemma rwPorP (x y : bool) : x \/ y <-> x || y.
Proof. by rewrite (rwP orP). Qed.

Lemma rwPandP (x y : bool) : x /\ y <-> x && y.
Proof. by rewrite (rwP andP). Qed.

Lemma rwPimplyP (x y : bool) : (x -> y) <-> x ==> y.
Proof. by rewrite (rwP implyP). Qed.

Lemma rwPnegP (x : bool) : (x -> False) <-> ~~ x.
Proof.  by move: (rwP (@negP x)); rewrite /not. Qed.

Global Hint Rewrite rwPeqP rwPorP rwPandP rwPimplyP rwPnegP : setdec_prop_to_bool.

Global Hint Rewrite orbF orFb andTb andbT implyTb Bool.negb_involutive : setdec_bool_simp.

Elpi Tactic setform_reify.
Elpi Accumulate lp:{{
    pred mem o:term, o:term, o:term.
    mem {{ lp:X :: _     }} X {{ xH      }} :- !.
    mem {{ _    :: lp:XS }} X {{ BinPos.Pos.succ lp:N }} :- mem XS X N.

    pred close o:term.
    close {{ nil }} :- !.
    close {{ _ :: lp:XS }} :- close XS.

    pred quote-elt o:term, i:term, o:term.
    quote-elt Eltvars X {{ lp:N }} :- 
      mem Eltvars X RN,
      coq.reduction.cbv.norm RN N.

    pred quote-syn o:term, o:term, i:term, o:term.
    quote-syn Setvars Eltvars {{ setU lp:X lp:Y }} {{ FSS_union lp:SX lp:SY}} :- !,
      quote-syn Setvars Eltvars X SX,
      quote-syn Setvars Eltvars Y SY.
    quote-syn Setvars Eltvars {{ setD lp:X lp:Y }} {{ FSS_diff lp:SX lp:SY}} :- !,
      quote-syn Setvars Eltvars X SX,
      quote-syn Setvars Eltvars Y SY.
    quote-syn Setvars Eltvars {{ setI lp:X lp:Y }} {{ FSS_inter lp:SX lp:SY}} :- !,
      quote-syn Setvars Eltvars X SX,
      quote-syn Setvars Eltvars Y SY.
    quote-syn _Setvars Eltvars {{ set1 lp:X }} {{ FSS_single lp:EX }} :- !,
      quote-elt Eltvars X EX.
    quote-syn _Setvars _Eltvars {{ lp:X }} {{ FSS_empty }} :-
      coq.unify-eq X {{ set0 }} ok.
    quote-syn _Setvars _Eltvars {{ lp:X }} {{ FSS_full }} :-
      coq.unify-eq X {{ setT }} ok.
    quote-syn Setvars _Eltvars X {{ FSS_var lp:N }} :-
      mem Setvars X RN,
      coq.reduction.cbv.norm RN N.

    pred quote-form i:term, o:term, o:term, i:term, o:term.
    quote-form _T Setvars Eltvars 
        {{ @eq_op lp:S lp:X lp:Y }} {{ F_Pred (FSP_Eqset lp:PX lp:PY)}}:- 
      coq.unify-eq S {{ finset_set_of__canonical__eqtype_Equality _ }} ok,
      quote-syn Setvars Eltvars X PX,
      quote-syn Setvars Eltvars Y PY.
    quote-form T _Setvars Eltvars 
        {{ @eq_op lp:T lp:X lp:Y }} {{ F_Pred (FSP_Eqelt (FE_var lp:PX) (FE_var lp:PY)) }}:- !,
      quote-elt Eltvars X PX,
      quote-elt Eltvars Y PY.
    quote-form _T Setvars Eltvars 
        {{ in_mem lp:X (mem (@pred_of_set _ lp:Y)) }} {{ F_Pred (FSP_In (FE_var lp:PX) lp:PY)}}:- !,
      quote-elt Eltvars X PX,
      quote-syn Setvars Eltvars Y PY.
    quote-form _T Setvars Eltvars 
        {{ subset (mem (@pred_of_set _ lp:X)) (mem (@pred_of_set _ lp:Y)) }} {{ F_Pred (FSP_Sub lp:PX lp:PY)}}:- !,
      quote-syn Setvars Eltvars X PX,
      quote-syn Setvars Eltvars Y PY.
    quote-form T Setvars Eltvars {{ negb lp:X }} {{ F_Not lp:FX }}:- !,
      quote-form T Setvars Eltvars X FX.
    quote-form T Setvars Eltvars {{ andb lp:X lp:Y }} {{ F_And lp:FX lp:FY }}:- !,
      quote-form T Setvars Eltvars X FX,
      quote-form T Setvars Eltvars Y FY.
    quote-form T Setvars Eltvars {{ orb lp:X lp:Y }} {{ F_Or lp:FX lp:FY }}:- !,
      quote-form T Setvars Eltvars X FX,
      quote-form T Setvars Eltvars Y FY.
    quote-form T Setvars Eltvars {{ implb lp:X lp:Y }} {{ F_Imply lp:FX lp:FY }}:- !,
      quote-form T Setvars Eltvars X FX,
      quote-form T Setvars Eltvars Y FY.
    quote-form  _ _ _ _ _ :- !,
      coq.say "Wrong set formula".

    solve (goal _Ctx _ {{ is_true lp:Goal }} _ [] as G) GL :-
    coq.elaborate-skeleton Goal {{ bool }} EGoal ok,
    quote-form _FT Setvars Eltvars EGoal FGoal,
    close Setvars,
    close Eltvars,
    coq.elaborate-skeleton 
        {{ _ : valid_form lp:Setvars lp:Eltvars (fun x y => None) lp:FGoal}} _ Res ok,
    refine Res G GL.
}}.
Elpi Typecheck.

(*  
  setdec_bool is about 5-10x faster than the setdec implemented in MSetDecide.v
  while the setdec here is 2-3x slower than setdec_bool.
  Maybe the performance of the autorewrite tactic or even the rewrite tactic
  is the bottleneck in simple cases.
*)

(* T is not used currently *)
Ltac setdec_bool :=
  autorewrite with setdec_unfold;
  elpi setform_reify;
  apply: (@set_decide_sound _ _ _ (Nat.of_num_uint 10000%uint)); vm_compute; 
  reflexivity.
  
Ltac setdec :=
  autorewrite with setdec_unfold;
  unfold not;
  unfold iff;
  autorewrite with setdec_prop_to_bool;
  autorewrite with setdec_bool_simp;
  elpi setform_reify;
  apply: (@set_decide_sound _ _ _ (Nat.of_num_uint 10000%uint)); vm_compute; 
  reflexivity.

(* test cases *)

Lemma tb0 (T : finType) (A B : {set T}) (x : T) :
  (A \subset B) ==> (x \in A) ==> (x \in B).
Proof.
  time setdec_bool.
Defined.

Lemma t0 (T : finType) (A B : {set T}) (x : T) :
  (A \subset B) -> (x \in A) -> (x \in B).
Proof.
  time setdec.
Defined.

Lemma tb1 (T : finType) (x y : T) :
  [set x;y] == [set y;x;x].
Proof.
  time setdec_bool.
Qed.

Lemma t1 (T : finType) (x y : T) :
  [set x;y] = [set y;x;x].
Proof.
  time setdec.
Qed.

(* seq not supported
Lemma t2 (T : finType) (x y : T) :
[set e in [:: y;x]] = [set e in [:: x;y;x]].
Proof.
setdec.
Abort. 
  *)

Lemma tb2 (A B : {set 'I_3}) : (A :|: B == A) ==> (B \subset A).
Proof.
  time setdec_bool.
Qed.

Lemma t2 (A B : {set 'I_3}) : (A :|: B == A) -> (B \subset A).
Proof.
  time setdec.
Qed.

Local Definition o0 := @Ordinal 3 0 erefl.
Local Definition o1 := @Ordinal 3 1 erefl.
Local Definition o2 := @Ordinal 3 2 erefl.

Lemma tb3 (A B : {set 'I_3}) (x y : 'I_3):
  (([set o0; x] \subset A) && ([set o1; y] \subset B))
    ==> (([set o0; x; y] \subset (setU B A))).
Proof.
  time setdec_bool.
Qed.

Lemma t3 (A B : {set 'I_3}) (x y : 'I_3):
  (([set o0; x] \subset A) /\ ([set o1; y] \subset B))
    -> (([set o0; x; y] \subset (setU B A))).
Proof.
  time setdec.
Qed.

Lemma tb4 (T : finType) (A B : {set T}) :
  [disjoint A & B] ==> [disjoint B & A].
(* A `&` B = set0 -> B `&` A = set0. *)
Proof.
  time setdec_bool.
Qed.

Lemma t4 (T : finType) (A B : {set T}) :
  [disjoint A & B] -> [disjoint B & A].
(* A `&` B = set0 -> B `&` A = set0. *)
Proof.
  time setdec.
Qed.

Lemma tb5 (T : finType) (f2 f4 f0 : {set T}) :
  (f2 :&: f2 == set0) ==> 
  (f0 :&: (f2 :|: f4) == set0) ==>
  (f0 :&: f2 == set0) ==>
  ~~ ((f0 :|: f2) :&: f4 != set0).
Proof.
  time setdec_bool.
Qed.

Lemma t5 (T : finType) (f2 f4 f0 : {set T}) :
  (f2 :&: f2 = set0) -> 
  (f0 :&: (f2 :|: f4) = set0) ->
  (f0 :&: f2 = set0) ->
  ~ ((f0 :|: f2) :&: f4 <> set0).
Proof.
  time setdec.
Qed.

Section Examples.
Variable (T : finType).

Lemma test_eq_trans_1 : forall x y z (s : {set T}),
  x = y ->
  ~ ~ z = y ->
  x \in s ->
  z \in s.
Proof.  
  move=> x y z s.
  setdec. 
Qed.

Lemma test_eq_trans_2 : forall (x y z : T) (r s : {set T}),
  x \in (set1 y) ->
  ~ z \in r ->
  ~ ~ z \in (y |: r) ->
  x \in s ->
  z \in s.
Proof. 
  move=> x y z r s.
  setdec. 
Qed.

Lemma test_eq_neq_trans_1 : forall w x y z (s : {set T}),
  x = w ->
  ~ ~ x = y ->
  ~ y = z ->
  w \in s ->
  w \in (s :\ z).
Proof. 
  move=> w x y z s.
  setdec. 
Qed.

(*
  The performance on this example is much worse than the Ltac implementation of 
  the same decision procedure.
  Maybe the reason is the lack of substitution in setforms.
*)
Lemma test_eq_neq_trans_2 : forall w x y z (r1 r2 s : {set T}),
  x \in (set1 w) ->
  ~ x \in r1 ->
  x \in (y |: r1) ->
  y \in  r2 ->
  y \in (r2 :\ z) ->
  w \in s ->
  w \in (s :\ z).
Proof. 
  move=> w x y z r1 r2 s.  
  unfold not.
  autorewrite with setdec_prop_to_bool.
  time setdec_bool. 
Qed.

Lemma test_In_singleton : forall (x : T),
  x \in (set1 x).
Proof. move=> x. setdec. Qed.

Lemma test_add_In : forall x y (s : {set T}),
  x \in (y |: s) ->
  ~ x = y ->
  x \in s.
Proof. move=> x y s. setdec. Qed.

Lemma test_Subset_add_remove : forall x (s : {set T}),
  s \subset (x |: (s :\ x)).
Proof. move=> x s. setdec. Qed.

Lemma test_eq_disjunction : forall w x y z : T,
  w \in (x |: (y |: (set1 z))) ->
  w = x \/ w = y \/ w = z.
Proof. move=> w x y z. setdec. Qed.

Lemma test_not_In_disj : forall x y s1 s2 s3 (s4 : {set T}),
  ~ x \in (setU s1 (setU s2 (setU s3 (y |: s4)))) ->
  ~ (x \in s1 \/ x \in s4 \/ y = x).
Proof. move=> x y s1 s2 s3 s4. setdec. Qed.

Lemma test_not_In_conj : forall x y s1 s2 s3 (s4 : {set T}),
  ~ x \in (setU s1 (setU s2 (setU s3 (y |: s4)))) ->
  ~ x \in s1 /\ ~ x \in s4 /\ ~ x = y.
Proof. move=> x y s1 s2 s3 s4. setdec. Qed.

Lemma test_iff_conj : forall a x (s s' : {set T}),
(a \in s' <-> x = a \/ a \in s) ->
(a \in s' <-> a \in (x |: s)).
Proof. move=> a x s s'. setdec. Qed.

(* cut rule needed *)
(* Lemma test_set_ops_1 : forall x q r (s : {set T}),
  (set1 x) \subset s ->
  (setU q r) = set0 ->
  (setI (setD s q) (setD s r)) = set0 ->
  ~ x \in s.
Proof. 
  move=> x q r s.
  unfold not.
  autorewrite with setdec_prop_to_bool. 
  elpi setform_reify. *)

(* cut rule needed *)
(* Lemma eq_chain_test : forall x1 x2 x3 x4 (s1 s2 s3 s4 : {set T}),
  s1 = set0 ->
  x2 \in (x1 |: s1) ->
  x3 \in s2 ->
  ~ x3 \in (s2 :\ x2) ->
  ~ x4 \in s3 ->
  x4 \in (x3 |: s3) ->
  x1 \in s4 ->
  (x4 |: s4) \subset s4.
Proof. 
  move=> x1 x2 x3 x4 s1 s2 s3 s4. *)

Lemma test_too_complex : forall (x y z : T) (r s : {set T}),
  x = y ->
  (x \in (set1 y) -> r \subset s) ->
  z \in r ->
  z \in s.
Proof.
  (** [setdec] is not intendd to solve this directly. *)
  intros until s; setdec.
Qed.

Lemma function_test_1 :
  forall (f : {set T} -> {set T}),
  forall (g : T -> T),
  forall (s1 s2 : {set T}),
  forall (x1 x2 : T),
  s1 = (f s2) ->
  x1 = (g (g x2)) ->
  x1 \in s1 ->
  (g (g x2)) \in (f s2).
Proof. 
  move=> f g s1 s2 x1 x2. 
  setdec. 
Qed.

(* setdec in MSetDecide.v cannot solve this directly *)
Lemma function_test_2 :
  forall (f : {set T} -> {set T}),
  forall (g : T -> T),
  forall (s1 s2 : {set T}),
  forall (x1 x2 : T),
  s1 = (f s2) ->
  x1 = (g x2) ->
  x1 \in s1 ->
  g x2 = g (g x2) ->
  (g (g x2)) \in (f s2).
Proof.
  move=> f g s1 s2 x1 x2. 
  setdec.
Qed.

Lemma test_baydemir :
  forall (f : {set T} -> {set T}),
  forall (s : {set T}),
  forall (x y : T),
  x \in (y |: (f s)) ->
  ~ x = y ->
  x \in (f s).
Proof. move=> f s x y. setdec. Qed.

Lemma test_seq (a b c : T):
  [set b; b; c; a; a; a; b] :\: (set1 a) :|: (set1 a) \subset [set a; b; c] .
Proof. setdec. Qed.

Lemma test_comp_comp (A : {set T}) :
  ~: (~: A) = A.
  Proof. setdec. Qed.

Lemma test_union_comp (A : {set T}) :
  A :|: (~: A) = setT.
  Proof. setdec. Qed.

Lemma test_inter_comp (A : {set T}) :
  A :&: (~: A) = set0.
  Proof. setdec. Qed.

Lemma test_diff_comp (A : {set T}) :
  A :\: (~: A) = A.
  Proof. setdec. Qed.

Lemma test_comp_setT (A : {set T}) :
  ~: setT = (set0 : {set T}).
  Proof. setdec. Qed.

Lemma test_comp_set0 (A : {set T}) :
  ~: set0 = (setT : {set T}).
  Proof. setdec. Qed.

End Examples.
