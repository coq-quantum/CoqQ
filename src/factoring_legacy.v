From mathcomp Require Import all_ssreflect.
From quantum Require Import compat.
(*
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory GRing Num.Theory Order.Theory.
(* Local Open Scope ring_scope.
Local Open Scope quotient_scope. *)

Module ContFraction.

Section ContFraction.
Import FracField.

(* Definition contFraction:= seq nat. *)

Implicit Type u: seq nat.
Implicit Type p q: int.
Implicit Type x y: rat.

Section CFE.

Fixpoint CFE_rec (n a b p1 q1 p2 q2 : nat) : nat * nat :=
  match n, a with
  | O, _ | _, O => (p1, q1)
  | S n, _ =>
    let c := (b %/ a) in
    CFE_rec n (b %% a) a (c * p1 + p2) (c * q1 + q2) p1 q1
  end.
Definition CFE n x : nat * nat :=
  CFE_rec n `|numq x| `|denq x| 0 1 1 0.

Lemma CFE0 x: CFE 0 x = (0, 1).
Proof. by []. Qed.

Lemma CFE1 x: `|numq x| <> 0 -> CFE 1 x = (1, `|denq x| %/ `|numq x|).
Proof.
  move => Hn;
  case Hnx: `|numq x|;
  by rewrite /CFE Hnx //= muln0 muln1 addn0 add0n.
Qed.

End CFE.

Section Seq2Rat.
(* Local Open Scope rat_scope. *)

(* numbers in seq are reduced by 1 *)
Fixpoint s2r_pair n u: nat * nat :=
  match n, u with
  | _, [::] | O, _ => (0, 1)
  | S n, h :: t =>
    ((s2r_pair n t).2, (s2r_pair n t).2 * h.+1 + (s2r_pair n t).1)
  end.

Lemma s2r_subproof n u :
  let v := ((s2r_pair n u).1 %:Z%Z, (s2r_pair n u).2 %:Z%Z) in
  (0%Z < v.2)%R && coprime `|v.1| `|v.2|.
Proof.
  apply /andP.
  rewrite !absz_nat ltz_nat;
  elim: n u => [|n' IHn] [|h t] //=;
  pose nn := (s2r_pair n' t).1;
  pose dd := (s2r_pair n' t).2.
  split.
  - by apply: ltn_addr;
    rewrite muln_gt0 (proj1 (IHn t)).
  - by rewrite -coprime_modr mulnC modnMDl
    coprime_sym coprime_modl (proj2 (IHn t)).
Qed.

Lemma s2rp_snd_gt0 n u:
  (0 < (s2r_pair n u).2)%N.
Proof.
  move: (s2r_subproof n u) => /andP /proj1.
  by case: (s2r_pair n u).
Qed.

Definition s2r n u: rat := Rat (s2r_subproof n u).

Lemma eq_properfrac p q x y
  (H: (p%:Q + x)%R = (q%:Q + y)%R)
  (Hxge0: (0 <= x)%R) (Hxlt1: (x < 1)%R)
  (Hyge0: (0 <= y)%R) (Hylt1: (y < 1)%R):
    x = y.
Proof.
  have Heq: ((p - q)%:Q%R = (y - x)%R) by
    rewrite mulrzBr addrC -[RHS](addKr (q%:Q)%R);
    f_equal; rewrite addrA -H addrK.
  case /intP Hpq: (p - q)%R => [|n|n].
  - move: Heq;
    rewrite Hpq mulr0z => Hxy.
    by rewrite -[RHS](addrNK x) -Hxy add0r.
  - have: ((y - x) < 1)%R
      by apply: ltr_naddr; rewrite ?oppr_le0.
    by rewrite -Heq Hpq -{2}(mulr1z 1) ltr_int.
  - have: (-1 < (y - x))%R
      by apply: ltr_paddl; rewrite ?ltr_opp2.
    by rewrite -Heq Hpq -(mulrN1z 1) ltr_int.
Qed.

Lemma eq_floorint p q x y
  (H: (p%:Q + x)%R = (q%:Q + y)%R)
  (Hxge0: (0 <= x)%R) (Hxlt1: (x < 1)%R)
  (Hyge0: (0 <= y)%R) (Hylt1: (y < 1)%R):
    p = q.
Proof.
  have: ((p - q)%:Q%R = (y - x)%R) by
    rewrite mulrzBr addrC -[RHS](addKr (q%:Q)%R);
    f_equal; rewrite addrA -H addrK.
  have ->: x = y by apply: (eq_properfrac H).
  rewrite addrN -(mulr0z 1);
  move => /intr_inj; exact: subr0_eq.
Qed.

Lemma eq_int_dem p q x y
  (H: (p%:Q + x)%R = (q%:Q + y)%R)
  (Hxge0: (0 <= x)%R) (Hxlt1: (x < 1)%R)
  (Hyge0: (0 <= y)%R) (Hylt1: (y < 1)%R):
    p = q /\ x = y.
Proof.
  split.
  - by apply: (eq_floorint H).
  - by apply: (eq_properfrac H).
Qed.

Lemma nude_le1 x:
  (numq x <= denq x)%R = (x <= 1)%R.
Proof.
  rewrite -{3}[x]divq_num_den ler_pdivr_mulr.
  - by rewrite mul1r ler_int.
  - by rewrite ltr0z denq_gt0.
Qed.

(* ugly!!!? *)
Lemma s2r_eq0 n u:
  s2r n u = 0%R <-> (s2r_pair n u).1 = 0.
Proof.
  split.
  move => /eqP;
  rewrite -numq_eq0 /s2r /numq => /eqP /=;
  case: (s2r_pair n u) => /= a b Ha;
  by inversion Ha.
  move => H1.
  apply /eqP.
  rewrite -numq_eq0 /s2r /numq /=.
  move: H1.
  by case: (s2r_pair n u) => /= a _ ->.
Qed.

Lemma rat_eqP x y:
  reflect (numq x = numq y /\ denq x = denq y) (x == y).
Proof.
  apply: (iffP idP) => [/eqP ->//|[/eqP Hn /eqP Hd]].
  by rewrite rat_eqE Hn Hd.
Qed.

Lemma s2r_nil n: s2r n [::] = 0%Q.
Proof.
  by case: n =>[|n];
  apply /eqP /rat_eqP; split.
Qed.

Lemma s2r_0 u: s2r 0 u = 0%Q.
Proof.
  by case: u => [|h t];
  apply /eqP /rat_eqP; split.
Qed.

Lemma s2r_le1 n u: (s2r n u <= 1)%R.
Proof.
  rewrite /s2r -nude_le1 /numq /denq /=.
  move: n u => [|n'] [|h t] //=.
  by rewrite lez_nat mulnS -addnA leq_addr.
Qed.

Lemma s2r_gt0_iff n u:
  if n is O then s2r n u = 0%R
    else if u is [::] then s2r n u = 0%R
      else (s2r n u > 0)%R.
Proof.
  move: n u => [|n'] [|h t];
  rewrite ?s2r_eq0 // /s2r -numq_gt0 /numq /=.
  exact: s2rp_snd_gt0.
Qed.

Lemma s2r_gt0 n h t:
  (s2r n.+1 (h::t) > 0)%R.
Proof.
  exact: (s2r_gt0_iff n.+1 (h::t)).
Qed.

Lemma denq_s2r_rec n h t:
  denq (s2r n.+1 (h::t)) = (denq (s2r n t) * h.+1 + numq (s2r n t))%R.
Proof. by []. Qed.

Lemma numq_s2r_rec n h t:
  numq (s2r n.+1 (h::t)) = denq (s2r n t).
Proof. by []. Qed.

Lemma pngt0 x:
  (x > 0)%R ->
  let: (@Rat (nx,dx) _) := x in
  (nx > 0)%R.
Proof.
  have ->: (x > 0)%R = lt_rat zeroq x by [].
  move: x => [[nx dx] prf] /=.
  by rewrite mul0r mulr1.
Qed.

Lemma pnge0 x:
  (x >= 0)%R ->
  let: (@Rat (nx,dx) _) := x in
  (nx >= 0)%R.
Proof.
  have ->: (x >= 0)%R = le_rat zeroq x by [].
  move: x => [[nx dx] prf] /=.
  by rewrite mul0r mulr1.
Qed.

Lemma gt0_lt0f (R: numDomainType) (x: R):
  (0 < x)%R -> (x < 0)%R = false.
Proof.
  move => P1. apply /negP.
  move => /(lt_trans P1).
  by rewrite ltxx.
Qed.

Lemma gt0_le0f (R: numDomainType) (x: R):
  (0 < x)%R -> (x <= 0)%R = false.
Proof.
  move => P1. apply /negP.
  move => /(lt_le_trans P1).
  by rewrite ltxx.
Qed.

Lemma ge0_lt0f (R: numDomainType) (x: R):
  (0 <= x)%R -> (x < 0)%R = false.
Proof.
  move => P1. apply /negP.
  move => /(le_lt_trans P1).
  by rewrite ltxx.
Qed.

Lemma denq_inv x:
  (x > 0)%R -> denq (x^-1%Q) = numq x.
Proof.
  move => Hgt0.
  move: Hgt0 {+}Hgt0 => /lt0r_neq0 +/pngt0.
  move: x => [[nx dx] /= prf] /=.
  move: prf {+}prf => /andP [Hd Hcop] prf.
  rewrite -[X in (X != 0%Q)]valqK fracq_eq0 negb_or /=
    den_fracq /= -[X in (numq X)]valqK num_fracq /=.
  move => /andP [H1 H2] Hn.
  by rewrite H2 H1 /= -exprnP signr_addb
    (gt0_lt0f Hn) (gt0_lt0f Hd) expr0 !mul1r gcdnC.
Qed.

Lemma numq_inv x:
  (x > 0)%R -> numq (x^-1%Q) = denq x.
Proof.
  move => Hgt0.
  move: Hgt0 {+}Hgt0 => /lt0r_neq0 +/pngt0.
  move: x => [[nx dx] /= prf] /=.
  move: prf {+}prf => /andP [Hd Hcop] prf.
  rewrite -[X in (X != 0%Q)]valqK fracq_eq0 negb_or /=
    num_fracq /= -[X in (denq X)]valqK den_fracq /=.
  move => /andP [H1 H2] Hn.
  by rewrite H2 H1 /= -exprnP signr_addb
    (gt0_lt0f Hn) (gt0_lt0f Hd) expr0 !mul1r gcdnC.
Qed.

Lemma gcdzMDr q m n : gcdz (q * m + n) m = gcdz n m.
Proof. by rewrite -gcdz_modl modzMDl gcdz_modl. Qed.

Lemma mulz_sign_absP_modn (a: int) (b: nat):
  (0 <= a)%R -> ((-1) ^+ (a < 0)%R * Posz (`|a| %/ b))%R = (a %/ Posz b)%Z.
Proof.
  move => Ha.
  have ->: Posz (`|a| %/ b) = `|(a %/ Posz b)%Z|.
  move: b => [|b]; first by rewrite divn0 divz0.
  move: a Ha => [a|a];
  by rewrite /divz /= ?mul1n ?PeanoNat.Nat.add_0_r.
  have ->: (a < 0)%R = ((a %/ b)%Z < 0)%R.
  rewrite (ge0_lt0f Ha) ge0_lt0f //.
  move: b => [|b]; by rewrite ?divz0 ?divz_ge0.
  exact: mulz_sign_abs.
Qed.

Lemma numq_addn x (h: nat):
  (0 <= x)%R -> numq (h%:~R + x)%Q = (Posz h * denq x + numq x)%R.
Proof.
  move: x => [[nx dx] /= prf] /pnge0 Hn;
  move: prf {+}prf => /andP [Hd Hcop] prf.
  rewrite -[X in (_ + (numq X))%R]valqK num_fracq
   -[X in (denq X)]valqK den_fracq addq_def addq_subdefE /=.
  have ->: (valq h%:~R).1 = h
    by rewrite -{2}(numq_int h).
  have ->: (valq h%:~R).2 = 1%R
    by rewrite -(denq_int h).
  rewrite mul1r mulr1 num_fracq /= gt0_lt0f -?exprnP //=.
  have ->: (dx != 0)%R by apply lt0r_neq0.
  have ->: gcdn `|(Posz h * dx + nx)%R| `|dx| = `|gcdz nx dx|
    by rewrite -(gcdzMDr (Posz h)) /gcdz.
  have Hdvd: (gcdn `|nx| `|dx| %| dx)%Z by exact: dvdn_gcdr.
  rewrite !mulz_sign_absP_modn //.
  rewrite divzDl /= -?mulz_divA -?divz_nat ?gtz0_abs //.
  by apply: dvdz_mull.
  by rewrite ler_paddr // pmulr_lge0.
Qed.

Lemma denq_addn x (h: nat):
  (0 <= x)%R -> denq (h%:~R + x)%Q = denq x.
Proof.
  move: x => [[nx dx] /= prf] /pnge0 Hn;
  move: prf {+}prf => /andP [Hd Hcop] prf.
  rewrite -[X in _ = denq X]valqK den_fracq addq_def addq_subdefE /=.
  have ->: (valq h%:~R).1 = h
    by rewrite -{2}(numq_int h).
  have ->: (valq h%:~R).2 = 1%R
    by rewrite -(denq_int h).
  rewrite mul1r mulr1 den_fracq /=.
  by have ->: gcdn `|(Posz h * dx + nx)%R| `|dx| = `|gcdz nx dx|
    by rewrite -(gcdzMDr (Posz h)) /gcdz.
Qed.

(* Lemma addnr_frac (p q h: nat):
  (h%:~R + fracq (Posz p, Posz q))%Q = fracq (((h * q)%R + p)%R, Posz q).
Proof.
  apply /eqP.
  rewrite rat_eqE /=. *)

Lemma s2r_rec n h t:
  s2r n.+1 (h :: t) = ((h.+1%:Q + s2r n t)%R^-1)%R.
Proof.
  apply /eqP.
  rewrite rat_eq numq_s2r_rec denq_s2r_rec.
  have H1: (0 < (h.+1%:~R + s2r n t)%Q)%R
    by rewrite ltr_paddr ?ltr0Sn.
  by rewrite numq_inv ?denq_inv ?numq_addn ?denq_addn
    ?[(_ * (denq _))%R]mulrC.
Qed.

(* Lemma s2r_eq1 n u:
  u = [:: 0] <-> s2r n.+1 u = 1%R.
Proof.
  split => [->|]; first by rewrite s2r_rec s2r_nil.
  case: u => [|h t /eqP]; first by rewrite s2r_nil.
  rewrite s2r_rec -{2}invr1 (inj_eq invr_inj).
  case: h => [|a /eqP H]. admit.
  have Hgt2: ((a.+2%:~R + s2r n t)%Q >= 2%:Q)%R
  by apply: ler_paddr; rewrite ?ler_nat.
  by move: H Hgt2 ->.
Admitted. *)

Lemma s2r_lt1 n u:
  nth 0 u n != 0 -> (s2r n.+1 u < 1)%R.
Proof.
  case: n u => [|n] [|h t] //= H.
  - rewrite s2r_rec invf_lt1;
    by apply ltr_paddr;
    rewrite ?(ltr1z, ltr0z) // ltz_nat ltnS lt0n.
  - rewrite s2r_rec invf_lt1;
    apply ltr_spaddr;
    rewrite ?(ler1z, ler0z) //;
    (by case: t H => [|h' t' H];
    [rewrite nth_nil| apply: s2r_gt0]).
Qed.

Lemma s2r_recl n u:
  n.+1 < size u ->
  numq (s2r n.+2 u) =
    (numq (s2r n.+1 u) * (nth 0%N u n.+1).+1 + numq (s2r n u))%R /\
  denq (s2r n.+2 u) =
    (denq (s2r n.+1 u) * (nth 0%N u n.+1).+1 + denq (s2r n u))%R.
Proof.
  elim: n u => [|n' IHn] [|h [|h' [|h'' t2]]] // Hu;
  try by rewrite /s2r /denq /numq /= !mul1n !addn0
    mul1r addr0 PoszD PoszM mulrC.
  have ->: nth 0%N [:: h, h', h'' & t2] n'.+2
    = nth 0%N [:: h', h'' & t2] n'.+1 by [].
  (* ugly!!! *)
  split;
  [rewrite [numq (_ n'.+1 _)]numq_s2r_rec;
  rewrite [numq (_ n'.+2 _)]numq_s2r_rec;
  rewrite [numq (_ n'.+3 _)]numq_s2r_rec
  |rewrite [denq (_ n'.+1 _)]denq_s2r_rec;
  rewrite [denq (_ n'.+2 _)]denq_s2r_rec;
  rewrite [denq (_ n'.+3 _)]denq_s2r_rec].
  by apply: proj2 (IHn _ _).
  rewrite (proj1 (IHn _ _)) // (proj2 (IHn _ _)) //
    !mulrDl !addrA; f_equal;
  rewrite addrC addrA; f_equal;
  rewrite addrC; f_equal;
  by rewrite -mulrAC.
Qed.

Lemma s2r_injective u v n:
  s2r n.+1 u = s2r n.+1 v ->
  nth O u n != O ->
  nth O v n != O ->
  take n.+1 u = take n.+1 v.
Proof.
  elim: n u v => [|n IHn]
    [|hu [|hu' tu']] [|hv [|hv' tv']] //=;
  rewrite !s2r_rec ?s2r_0 ?s2r_nil ?addr0 ?nth_nil;
  move => /invr_inj //;
  try (
    by move => /intr_inj /eqP;
    rewrite eqz_nat eqSS;
    move => /eqP Huv _ _;
    rewrite Huv
  ).
  rewrite -!(s2r_rec n);
  move => Heq Hnu Hnv.
  have Int_Dem: (hu.+1%:Z = hv.+1%:Z)%R
      /\ s2r n.+1 (hu' :: tu') = s2r n.+1 (hv' :: tv')
  by exact: (eq_int_dem Heq _ (s2r_lt1 Hnu) _ (s2r_lt1 Hnv)).
  f_equal.
  - by apply /eqP;
    rewrite -(inj_eq succn_inj) -eqz_nat (proj1 Int_Dem).
  - by rewrite -!(take_cons n.+1) (IHn _ (hv'::tv')) ?(proj2 Int_Dem).
Qed.

End Seq2Rat.

Section Rat2Seq.
(* numbers in seq are reduced by 1 *)

Definition floorint x := `|denq x| %/ `|numq x|.
Lemma fl_gt0 x (Hx0: (x > 0)%R) (Hx1: (x <= 1)%R):
  floorint x > 0.
Admitted.

(* Does not end with 1 *)
Fixpoint r2s_rec (p q: nat) : seq nat :=
  if (p == 0) || (q == 0) then [::] else
  let p' := q %% p in if p' is O then [:: (q %/ p).-1] else
  if p - (p'.-1) is (q'.+1) then (q %/ p).-1 :: (p %/ p').-1 ::
    r2s_rec (q' %% p') p' else [::].

Definition r2s x :=
  r2s_rec `|numq x| `|denq x|.

(* Does end with 1 *)
Fixpoint r2s1_rec (p q: nat) : seq nat :=
  if (p == 0) || (q == 0) then [::] else
  let p' := q %% p in if p' is O then (q %/ p).-2 :: [:: O] else
  if p - (p'.-1) is (q'.+1) then (q %/ p).-1 :: (p %/ p').-1 ::
    r2s1_rec (q' %% p') p' else [::].

Definition r2s1 x :=
    r2s1_rec `|numq x| `|denq x|.

Definition cont_cano u :=
  match lastP u with
  | LastNil => u
  | LastRcons s x => 
    match lastP s, x with
    | LastRcons s' x', O => rcons s' x'.+1
    | _, _ => u
    end
  end.

Lemma r2s_rect x (Hx0: (x > 0)%R) (Hx1: (x <= 1)%R):
  r2s x = (floorint x).-1 :: r2s (x^-1 - (floorint x)%:Q).
Admitted.

(* Variant r2s_nil_cons x: seq nat -> Type := *)

Lemma r2s_injective x y:
  r2s x = r2s y -> x = y.
Proof.
  elim: (r2s x) y => [|h t IHs] y.
Admitted.

End Rat2Seq.

Lemma r2sK x:
  forall N, exists n, n > N /\ s2r n (r2s x) = x.
Proof. Admitted.

Lemma s2rK u:
  exists N, forall n, n > N -> r2s (s2r n u) = cont_cano u.
Proof. Admitted.

Lemma cont_close_prefix (x y: rat):
  (`|x - y| <= (2 * (denq y)%:Q ^+2)^-1)%R
  -> exists t, s2r t (r2s x) = y.
Proof.
  move => Hcls.
  have [t Hc]: exists t, (`|s2r t (r2s x) - x| <= (2 * (denq y)%:Q ^+2)^-1)%R.
  admit.
  exists t.
  have:(`|s2r t (r2s x) - y| <= (denq y)%:Q ^-2)%R.
  admit.
  admit.
Admitted.


  have: 0 < z /\ z < 1.
  have: (r2s y) ++ (r2s z) = (r2s x).
  have: take n.+1 (r2s x) = take n.+1 (r2s y).

  exists n, s2r n.+1
Admitted.

End ContFraction.
End ContFraction.

(* Variable R: idomainType.

Definition contFraction:= seq R.

Implicit Type u: contFraction.
Implicit Type p q: R.
Implicit Type x y: ratio R.
Notation "x %:F"  := (tofrac x).

Fixpoint cont2ratio u: {ratio R} :=
  match u with
  | [::] => Ratio 0 1
  | h :: t => let (n, d):= frac (cont2ratio t) in
              Ratio (h * n + d) n
  end.

(* Does not end with 1 *)
Fixpoint ratio2cont x :=
  let e := edivp \n_(repr x) \d_(repr x) in
  if e.2 == 0 then [::e.1] else e.1 :: frac2cont (x - e.1 %:F)^-1. *)

(* Variable R: idomainType.

Definition contFraction:= seq R.

Implicit Type u: contFraction.
Implicit Type p q: R.
Implicit Type x y: {fraction R}.
Notation "x %:F"  := (tofrac x).

Fixpoint cont2frac u :=
  match u with
  | [::] => 0 %:F
  | h :: t => h %:F + (cont2frac t)^-1
  end.

(* Does not end with 1 *)
Fixpoint frac2cont x :=
  let e := edivp \n_(repr x) \d_(repr x) in
  if e.2 == 0 then [::e.1] else e.1 :: frac2cont (x - e.1 %:F)^-1. *)

(* Local Open Scope int_scope.
Definition contFraction:= seq int.

Implicit Type u: contFraction.
Implicit Type p q: int.
Implicit Type x y: {fraction int}.
Notation "x %:F"  := (tofrac x).

Fixpoint cont2frac u: {fraction int} :=
  match u with
  | [::] => 0 %:F
  | h :: t => h %:F + (cont2frac t)^-1
  end.

Locate "%/".
(* Does not end with 1 *)
Fixpoint frac2cont x :=
  let (p,q) := (\n_(repr x), \d_(repr x)) in
  if p %% q == 0 then [::p %/ q] else (p %/ q) :: (frac2cont ((x - (divz p q) %:F)^-1)). *)
*)